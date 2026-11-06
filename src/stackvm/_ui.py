from __future__ import annotations

import asyncio
import itertools as it
import platform
from collections.abc import Callable
from concurrent.futures import Future
from dataclasses import dataclass
from functools import cache, partial
from importlib import metadata, resources
from io import IOBase, StringIO
from random import Random
from types import CoroutineType, NoneType, SimpleNamespace
from typing import Any, ClassVar, cast
from weakref import WeakKeyDictionary

import flet as ft

from stackvm._api import Executor, StackMachine
from stackvm._util import Instruction as VMInstruction
from stackvm._util import StackItem, VMFrame


@cache
def monospace(size: int = 24) -> ft.TextStyle:
    return ft.TextStyle(
        size=size,
        font_family="JetBrains Mono",
        font_family_fallback=["Fira Code", "Consolas", "Inconsolata", "SF Mono", "Monospace"],
    )


COLORS: dict[type, ft.Colors] = {
    NoneType: ft.Colors.GREY_600,
    bool: ft.Colors.BLUE_600,
    int: ft.Colors.GREEN_600,
    float: ft.Colors.ORANGE_600,
    str: ft.Colors.PURPLE_600,
    bytes: ft.Colors.BROWN_600,
    slice: ft.Colors.CYAN_600,
    list: ft.Colors.RED_600,
    dict: ft.Colors.YELLOW_600,
}


async def loop(
    page: ft.Page,
    executor: Executor,
    pause: asyncio.Event,
    send: asyncio.Queue[tuple[bool, Any]],
    receive: asyncio.Queue[float],
) -> object:
    await send.put((False, -1))
    delay = await receive.get()
    await asyncio.sleep(delay)
    while True:
        await pause.wait()
        current = executor.state.frames[-1].current

        try:
            returned, value = await asyncio.create_task(asyncio.to_thread(executor.step))
        except BaseException as e:  # noqa: BLE001
            await send.put((True, (current, e)))
            break

        if returned:
            await send.put((True, (current, value)))
            return

        await send.put((False, current))
        delay = await receive.get()

        if pause.is_set():  # spam clicking step is okay
            await asyncio.sleep(delay)


ITEM_HEIGHT = 50


def item_height(obj: object) -> float:
    if isinstance(obj, list):
        return ITEM_HEIGHT + sum(item_height(i) for i in obj)

    if isinstance(obj, dict):
        return ITEM_HEIGHT + sum(max(item_height(k), item_height(v)) for k, v in obj.items())

    return ITEM_HEIGHT


@ft.control
class Item(ft.Container):
    @property
    def item(self) -> object:
        return self.data

    @property
    def app(self) -> App:
        try:
            return self.page.data
        except RuntimeError:
            return ft.context.page.data

    def init(self):
        obj = self.item
        color = COLORS.get(type(obj), ft.Colors.PINK_600)

        self.bgcolor = color
        self.border = ft.Border.all(2, ft.Colors.BLACK)

        self.height = item_height(obj)
        self.border_radius = ITEM_HEIGHT / 5

    def before_update(self):
        obj = self.item
        size = 24

        if isinstance(obj, IOBase):
            obj_repr = f"File: {getattr(obj, 'name', '<unknown>')}"
        elif isinstance(obj, list):
            obj_repr = "List: []" if not obj else "List:"
        elif isinstance(obj, dict):
            obj_repr = "Dictionary: {}" if not obj else "Dictionary:"
        else:
            obj_repr = repr(obj)

        text = ft.Row(
            [
                ft.Text(
                    obj_repr,
                    style=monospace(size),
                    text_align=ft.TextAlign.CENTER,
                    align=ft.Alignment.CENTER,
                    color=ft.Colors.BLACK if isinstance(obj, dict) else ft.Colors.WHITE,
                )
            ],
            scroll=ft.ScrollMode.AUTO,
            spacing=0,
            alignment=ft.MainAxisAlignment.CENTER,
        )

        if obj and isinstance(obj, list):
            children = [Item(data=item) for item in obj]
            self.content = ft.Column(
                cast(
                    list[ft.Control],
                    [
                        text,
                        ft.Container(
                            ft.Column(cast(list[ft.Control], children), spacing=0),
                            padding=ft.Padding.symmetric(horizontal=4),
                        ),
                    ],
                )
            )
        elif obj and isinstance(obj, dict):
            children = [
                ft.Row([Item(data=key, expand=1), Item(data=value, expand=1)], spacing=0) for key, value in obj.items()
            ]
            self.content = ft.Column(
                cast(
                    list[ft.Control],
                    [
                        text,
                        ft.Container(
                            ft.Column(cast(list[ft.Control], children), spacing=0),
                            padding=ft.Padding.symmetric(horizontal=5),
                        ),
                    ],
                )
            )
        else:
            self.content = text

    def build(self) -> None:
        self.set_animation()

    def set_animation(self) -> None:
        self.animate = ft.Animation(int((self.app.state.delay * 1000) // 2), ft.AnimationCurve.EASE_IN_OUT)
        self.animate_size = ft.Animation(int((self.app.state.delay * 1000) // 2), ft.AnimationCurve.EASE_IN_OUT)
        self.animate_offset = ft.Animation(int((self.app.state.delay * 1000) // 2), ft.AnimationCurve.EASE_IN_OUT)


@ft.control
class Instruction(ft.Container):
    @property
    def index(self) -> VMInstruction:
        return self.data.index

    @property
    def instruction(self) -> VMInstruction:
        return self.data.instruction

    @property
    def current(self) -> bool:
        return self.data.current

    @current.setter
    def current(self, value: bool) -> None:
        self.data.current = value

    @property
    def text(self) -> str:
        return self.data.text

    @text.setter
    def text(self, value: str) -> None:
        self.data.text = value

    @property
    def app(self) -> App:
        try:
            return self.page.data
        except RuntimeError:
            return ft.context.page.data

    def init(self):
        self.data = SimpleNamespace(index=self.data[0], instruction=self.data[1], current=False)

        instr = self.instruction
        color = ft.Colors.WHITE

        size = 24

        self.text = f"{self.index}: {instr}"

        control: list[ft.Control] = [
            ft.Text(
                self.text,
                style=monospace(size),
                text_align=ft.TextAlign.CENTER,
                align=ft.Alignment.CENTER,
            )
        ]

        self.content = ft.Row(
            control,
            scroll=ft.ScrollMode.AUTO,
            spacing=0,
            alignment=ft.MainAxisAlignment.CENTER,
        )
        self.bgcolor = color
        self.border = ft.Border.all(2, ft.Colors.BLACK)

        self.height = ITEM_HEIGHT
        self.border_radius = ITEM_HEIGHT / 5

    def before_update(self):
        control = cast(ft.Text, cast(ft.Row, self.content).controls[0])
        if self.current:
            control.value = f"▶️ {self.text} ◀️"
        else:
            control.value = self.text

        if self.current:
            control.color = ft.Colors.WHITE
        else:
            control.color = ft.Colors.BLACK

        self.animate = ft.Animation(int((self.app.state.delay * 1000) // 2), ft.AnimationCurve.EASE_IN_OUT)


@ft.control
class Stack(ft.Column):
    @property
    def items(self) -> list[StackItem]:
        return self.data.items

    @items.setter
    def items(self, items: list[StackItem]) -> None:
        self.data.last_items = self.items
        self.data.items = list(items)

    @property
    def positions(self) -> dict[StackItem, float]:
        return self.data.positions

    @positions.setter
    def positions(self, positions: dict[StackItem, float]) -> None:
        self.data.positions = dict(positions.items())

    @property
    def last_items(self) -> list[StackItem]:
        return self.data.last_items

    @property
    def item_controls(self) -> WeakKeyDictionary[StackItem, Item]:
        return self.data.item_controls

    @property
    def app(self) -> App:
        try:
            return self.page.data
        except RuntimeError:
            return ft.context.page.data

    def init(self):
        self.expand = 1
        self.scroll = ft.ScrollMode.AUTO

        self.data = SimpleNamespace(items=[], last_items=[], positions={}, item_controls=WeakKeyDictionary())

    def before_update(self):
        old_items = list(reversed(self.last_items))
        new_items = list(reversed(self.items))

        old_positions = self.positions

        for item in new_items:
            if item not in self.item_controls:
                self.item_controls[item] = Item(key=id(item), data=item.obj)

        leaving = set(old_items) - set(new_items)
        entering = set(new_items) - set(old_items)

        old_controls = [
            (item, self.item_controls[item]) for item in old_items + [i for i in new_items if i in entering]
        ]
        new_controls: list[tuple[StackItem, Item]] = [(item, self.item_controls[item]) for item in new_items]

        temporary_positions = dict(
            zip(
                (item for item, _ in old_controls),
                it.accumulate(
                    old_controls,
                    lambda prev, entry: prev + item_height(entry[0].obj) + self.spacing,
                    initial=0,
                ),
            )
        )
        new_positions = dict(
            zip(
                new_items,
                it.accumulate(
                    new_items,
                    lambda prev, item: prev + item_height(item.obj) + self.spacing,
                    initial=0,
                ),
            )
        )

        if old_positions == new_positions:
            # currently impossible for a mutable object to be mutated without affecting the stack
            return

        self.positions = new_positions

        positions: list[tuple[Item, tuple[tuple[float, float], tuple[float, float]]]] = []
        for item, control in old_controls:
            if item in leaving:
                end = (-2, 0)
            else:
                height = item_height(item.obj)
                diff = new_positions[item] - temporary_positions[item]
                end = (0, diff / height)

            start = (-2, end[1]) if item in entering else (0, 0)

            positions.append((control, (start, end)))

        async def animate():
            await asyncio.sleep(1 / 30)
            for item, control in new_controls:
                control.height = item_height(item.obj)
                control.update()
            for control, (_, end) in positions:
                control.offset = ft.Offset(*end)
                control.update()
            await asyncio.sleep(self.app.state.delay / 2)
            self.controls = [entry[1] for entry in new_controls]
            for control in cast(list[Item], self.controls):
                control.offset = ft.Offset(0, 0)
                control.animate_offset = None
            self.data.last_items = list(self.items)
            self.update()

        self.controls = [entry[1] for entry in old_controls]

        for control, (start, _) in positions:
            control.offset = ft.Offset(*start)
            control.set_animation()

        self.app.create_task(animate)


@ft.control
class Instructions(ft.Column):
    @property
    def instructions(self) -> tuple[VMInstruction, ...]:
        return self.data.instructions

    @property
    def current(self) -> int:
        return self.data.current

    @current.setter
    def current(self, value: int) -> None:
        self.data.prev = self.current
        self.data.current = value

    @property
    def next(self) -> int:
        return self.data.next

    @next.setter
    def next(self, value: int) -> None:
        self.data.next = value

    @property
    def suspended(self) -> list[int]:
        return self.data.suspended

    @suspended.setter
    def suspended(self, value: list[int]) -> None:
        self.data.suspended = value

    @property
    def viewport_height(self) -> float:
        return self.data.viewport_height

    @viewport_height.setter
    def viewport_height(self, value: float) -> None:
        self.data.viewport_height = value

    @property
    def prev(self) -> int:
        return self.data.prev

    @property
    def app(self) -> App:
        try:
            return self.page.data
        except RuntimeError:
            return ft.context.page.data

    def init(self):
        self.expand = 1
        self.scroll = ft.ScrollMode.AUTO

        self.data.current = 0
        self.data.next = 0
        self.data.prev = 0
        self.data.suspended = []
        self.data.viewport_height = 0

        self.controls = [
            Instruction(data=(index, instr), key=ft.ScrollKey(f"instr_{index}"))
            for index, instr in enumerate(self.instructions)
        ]

        self.offsets = list(
            it.accumulate(
                self.controls,
                lambda prev, control: prev + cast(float, cast(Instruction, control).height) + self.spacing,
                initial=0,
            )
        )

        def on_size_change(event: ft.LayoutSizeChangeEvent) -> None:
            self.viewport_height = event.height

        self.on_size_change = on_size_change

    def before_update(self) -> None:
        if 0 <= self.prev < len(self.controls):
            prev = self.prev
            control = cast(Instruction, self.controls[prev])
            control.current = False
            control.bgcolor = ft.Colors.WHITE

        if 0 <= self.next <= len(self.controls):
            control = cast(Instruction, self.controls[self.next])
            control.current = False
            control.bgcolor = ft.Colors.GREEN_200

        for suspended in self.suspended:
            if 0 <= suspended <= len(self.controls):
                control = cast(Instruction, self.controls[suspended])
                control.current = False
                control.bgcolor = ft.Colors.GREY_400

        if 0 <= self.current < len(self.controls):
            current = self.current
            control = cast(Instruction, self.controls[current])
            control.current = True
            control.bgcolor = ft.Colors.GREEN_800

            async def scroll(current: int = current):
                height = self.viewport_height
                await self.scroll_to(
                    max(self.offsets[current] - height / 2 + (0 if control.height is None else control.height / 2), 0),
                    duration=int(self.app.state.delay * 1000 // 2),
                )

            self.app.create_task(scroll)


@ft.control
class Frame(ft.Container):
    @property
    def frame(self) -> VMFrame:
        return self.data.frame

    @property
    def active(self) -> bool:
        return self.data.active

    @active.setter
    def active(self, value: bool) -> None:
        self.data.active = value

    @property
    def app(self) -> App:
        try:
            return self.page.data
        except RuntimeError:
            return ft.context.page.data

    def init(self):
        self.border = ft.Border.all(2, ft.Colors.BLACK)

        self.border_radius = ITEM_HEIGHT / 5

        self.expand = True

        self.data = SimpleNamespace(frame=self.data[0], active=self.data[1])

        self.set_animation()

    def before_update(self):
        self.set_animation()

        color = ft.Colors.GREEN_200 if self.active else ft.Colors.GREY_200
        grid_color = ft.Colors.GREEN_400 if self.active else ft.Colors.GREY_400

        self.bgcolor = color

        frame = self.frame

        size = 24

        text = f"Current: {frame.prev}\nNext: {frame.current}"

        content = ft.Column(
            [
                ft.Text(
                    text,
                    style=monospace(size),
                    expand=True,
                    text_align=ft.TextAlign.CENTER,
                )
            ],
            margin=ft.Margin.all(5),
            horizontal_alignment=ft.CrossAxisAlignment.STRETCH,
        )

        if frame.env:
            grid = ft.Container(
                ft.DataTable(
                    columns=[
                        ft.DataColumn(label=ft.Text("Variable", style=monospace(size))),
                        ft.DataColumn(label=ft.Text("Value", style=monospace(size))),
                    ],
                    rows=[
                        ft.DataRow(
                            cells=[
                                ft.DataCell(
                                    ft.Text(
                                        spans=[ft.TextSpan(str(key))]
                                        + (
                                            [ft.TextSpan(" (global)", style=monospace(size // 2))]
                                            if key in frame.env.maps[1] and key not in frame.env.maps[0]
                                            else []
                                        ),
                                        style=monospace(size),
                                    )
                                ),
                                ft.DataCell(
                                    ft.Row(
                                        [
                                            ft.Text(
                                                repr(value),
                                                style=monospace(size),
                                                no_wrap=True,
                                            )
                                        ],
                                        scroll=ft.ScrollMode.AUTO,
                                    ),
                                ),
                            ]
                        )
                        for key, value in sorted(frame.env.items())
                    ],
                    bgcolor=grid_color,
                    border=ft.Border.all(2, ft.Colors.BLACK),
                    border_radius=ITEM_HEIGHT / 5,
                    horizontal_lines=ft.BorderSide(1, ft.Colors.BLACK),
                    vertical_lines=ft.BorderSide(1, ft.Colors.BLACK),
                    horizontal_margin=4,
                    column_spacing=8,
                ),
                theme=ft.Theme(divider_theme=ft.DividerTheme(color=ft.Colors.BLACK, thickness=1)),
            )
            content.controls.append(grid)

        self.content = content

    def set_animation(self) -> None:
        pass


@ft.control
class CallStack(ft.Column):
    @property
    def executor(self) -> Executor:
        return self.data.executor

    @property
    def frames(self) -> list[VMFrame]:
        return self.executor.state.frames

    @property
    def frame_controls(self) -> dict[VMFrame, Frame]:
        return self.data.frame_controls

    @frame_controls.setter
    def frame_controls(self, value: dict[VMFrame, Frame]) -> None:
        self.data.frame_controls = value

    def init(self):
        self.expand = 2
        self.horizontal_alignment = ft.CrossAxisAlignment.STRETCH
        self.scroll = ft.ScrollMode.AUTO

        self.frame_controls = {}

    def before_update(self):
        controls: list[ft.Control] = []

        frames = list(reversed(self.frames))

        if not frames:
            return

        if frames[0] in self.frame_controls:
            control = self.frame_controls[frames[0]]
            control.active = True
            controls.append(control)
        else:
            control = Frame(data=(frames[0], True))
            self.frame_controls[frames[0]] = control
            controls.append(control)

        for frame in frames[1:]:
            control = self.frame_controls[frame]
            control.active = False
            controls.append(control)

        for frame in self.frame_controls.keys() - set(frames):
            del self.frame_controls[frame]

        self.controls = controls


@ft.control
class Console(ft.Container):
    @property
    def stdout(self) -> StringIO:
        return self.data

    @property
    def text(self) -> ft.Text:
        return cast(ft.Text, cast(ft.Column, self.content).controls[0])

    def init(self) -> None:
        self.bgcolor = ft.Colors.GREEN_900

        self.border = ft.Border.all(2, ft.Colors.BLACK)
        self.border_radius = ITEM_HEIGHT // 5

        self.expand = 1

        self.content = ft.Column(
            [
                ft.Text(
                    style=monospace(16),
                    color=ft.Colors.WHITE,
                    margin=ft.Margin.all(5),
                    selectable=True,
                )
            ],
            scroll=ft.ScrollMode.AUTO,
            auto_scroll=True,
        )

    def before_update(self) -> None:
        self.text.value = self.stdout.getvalue()


def ErrorDialog(page: ft.Page, exception: BaseException) -> ft.AlertDialog:
    def close() -> None:
        page.pop_dialog()

    return ft.AlertDialog(
        modal=True,
        title=ft.Text("Exception raised during execution"),
        content=ft.Text(f"{type(exception).__name__}: {exception}", style=monospace(14), selectable=True),
        actions=[ft.TextButton("OK", on_click=close)],
    )


def ReturnDialog(page: ft.Page, obj: object) -> ft.AlertDialog:
    def close() -> None:
        page.pop_dialog()

    return ft.AlertDialog(
        modal=True,
        title=ft.Text("Program finished successfully"),
        content=ft.Text(
            spans=[ft.TextSpan("Returned: "), ft.TextSpan(repr(obj), style=monospace(14))], selectable=True
        ),
        actions=[ft.TextButton("OK", on_click=close)],
    )


async def input_dialog(page: ft.Page, stdout: StringIO) -> str:
    future: asyncio.Future[str] = asyncio.Future()

    def submit(event: ft.Event[Any]):
        value = text_input.value or ""
        print(value, file=stdout)
        page.pop_dialog()
        if not future.done():
            future.set_result(value)

    text_input = ft.TextField(autofocus=True, on_submit=submit)

    dialog = ft.AlertDialog(
        modal=True,
        title=ft.Text("Input requested"),
        content=text_input,
        actions=cast(list[ft.Control], [ft.TextButton("Submit", on_click=submit)]),
    )

    page.show_dialog(dialog)

    return await future


def get_input_from_dialog(page: ft.Page, stdout: StringIO) -> str:
    result = asyncio.run_coroutine_threadsafe(input_dialog(page, stdout), page.loop)
    return result.result()


@ft.control
class SpeedSlider(ft.Slider):
    delays: ClassVar[tuple[float, ...]] = (1.25, 1.0, 0.75, 0.5, 0.25)

    @property
    def app(self) -> App:
        try:
            return self.page.data
        except RuntimeError:
            return ft.context.page.data

    def init(self):
        self.value = 2
        self.min = 0
        self.max = 4
        self.divisions = 4

        self.on_change = self.handle_change

        self.expand = True

        self.set_label()

    def set_label(self) -> None:
        value = 2 if self.value is None else int(self.value)
        self.label = ["Slowest", "Slow", "Medium", "Fast", "Fastest"][value]

    def handle_change(self, event: ft.Event[ft.Slider]):
        value = 2 if self.value is None else int(self.value)
        self.set_label()

        self.app.state.delay = self.delays[value]


@ft.control
class PauseButton(ft.IconButton):
    @property
    def pause(self) -> asyncio.Event:
        return self.data

    def init(self) -> None:
        self.icon = ft.Icons.PAUSE

        def on_click(event: ft.Event[ft.IconButton]):
            if self.pause.is_set():
                self.pause.clear()
                self.icon = ft.Icons.PLAY_ARROW
            else:
                self.pause.set()
                self.icon = ft.Icons.PAUSE

        self.on_click = on_click


@ft.control
class StepButton(ft.IconButton):
    @property
    def pause(self) -> asyncio.Event:
        return self.data

    def init(self) -> None:
        self.icon = ft.Icons.SKIP_NEXT

        async def on_click(event: ft.Event[ft.IconButton]):
            if not self.pause.is_set():
                self.pause.set()
                await asyncio.sleep(0)
                self.pause.clear()

        self.on_click = on_click


@dataclass
class AppState:
    delay: float = 0.75
    paused: bool = False


class App:
    page: ft.Page
    machine: StackMachine
    executor: Executor

    speed_control: ft.Row
    stack: Stack
    instructions: Instructions
    call_stack: CallStack
    console: Console

    stdout: StringIO

    pause: asyncio.Event
    send: asyncio.Queue[float]
    receive: asyncio.Queue[tuple[bool, Any]]

    state: AppState

    tasks: set[Future]

    result: Future[Any]

    closing: bool

    def __init__(
        self,
        machine: StackMachine,
        page: ft.Page,
        *,
        args: tuple[Any, ...],
        seed: int | str | Random | None = None,
        result: Future[Any],
    ) -> None:
        self.tasks = set()

        self.state = AppState()

        self.page = page
        page.data = self

        page.title = "StackVM"

        if platform.system() == "Windows":
            icon = resources.files("stackvm").joinpath("resources", "icon.ico")

            with resources.as_file(icon) as path:
                page.window.icon = str(path)

        self.machine = machine

        self.stdout = StringIO()
        self.executor = machine.ui_executor(
            *args, seed=seed, stdin=partial(get_input_from_dialog, page, self.stdout), stdout=self.stdout
        )

        self.pause = asyncio.Event()
        self.pause.set()

        self.send = asyncio.Queue()
        self.receive = asyncio.Queue()

        self.speed_control = ft.Row(
            [
                ft.Text("Speed:", size=18),
                SpeedSlider(0),
                PauseButton(data=self.pause),
                StepButton(data=self.pause),
                ft.IconButton(ft.Icons.STOP, icon_color=ft.Colors.RED, on_click=page.window.close),
            ],
        )

        self.stack = Stack()
        self.instructions = Instructions(data=SimpleNamespace(instructions=self.executor.instructions))
        self.call_stack = CallStack(data=SimpleNamespace(executor=self.executor))
        self.console = Console(data=self.stdout)

        page.theme = ft.Theme(color_scheme=ft.ColorScheme(primary=ft.Colors.GREEN))

        self.closing = False

        self.result = result

        name = metadata.metadata("stackvm").get("Name", "???")
        version = metadata.version("stackvm")
        author = metadata.metadata("stackvm").get("Author", "???")
        self.page.add(
            ft.Column(
                [
                    ft.Row(
                        [
                            ft.Column(
                                [ft.Text("Operand Stack", style=monospace(36))],
                                horizontal_alignment=ft.CrossAxisAlignment.CENTER,
                                expand=1,
                            ),
                            ft.Column(
                                [ft.Text("Instructions", style=monospace(36))],
                                horizontal_alignment=ft.CrossAxisAlignment.CENTER,
                                expand=1,
                            ),
                            ft.Column(
                                [ft.Text("Console", style=monospace(36))],
                                horizontal_alignment=ft.CrossAxisAlignment.CENTER,
                                expand=1,
                            ),
                        ]
                    ),
                    ft.Row(
                        [
                            self.stack,
                            self.instructions,
                            ft.Column(
                                [
                                    self.console,
                                    ft.Text("Call Stack", style=monospace(36), text_align=ft.TextAlign.CENTER),
                                    self.call_stack,
                                ],
                                expand=1,
                                horizontal_alignment=ft.CrossAxisAlignment.STRETCH,
                            ),
                        ],
                        expand=True,
                        vertical_alignment=ft.CrossAxisAlignment.START,
                    ),
                    self.speed_control,
                    ft.Row(
                        [ft.Text(f"{name} v{version} by {author}", style=monospace(12), color=ft.Colors.GREY_500)],
                        alignment=ft.MainAxisAlignment.END,
                    ),
                ],
                expand=True,
                horizontal_alignment=ft.CrossAxisAlignment.STRETCH,
            )
        )

        self.create_task(loop, page, self.executor, self.pause, self.receive, self.send)
        self.create_task(self.updateloop)

        async def on_window_event(event: ft.WindowEvent) -> None:
            if event.type == ft.WindowEventType.CLOSE:
                if self.closing:
                    return
                self.closing = True

                for task in list(self.tasks):
                    task.cancel()

                await asyncio.gather(*map(asyncio.wrap_future, self.tasks), return_exceptions=True)

                await page.window.destroy()

                self.result.set_result(None)

        page.window.prevent_close = True
        page.window.on_event = on_window_event

    async def updateloop(self) -> None:
        executor = self.executor
        while True:
            returned, value = await self.receive.get()

            if returned:
                current, value = value
            else:
                current = value

            if executor.state.frames:
                self.stack.items = executor.state.frames[-1].stack
            self.stack.update()

            self.instructions.current = current
            if executor.state.frames:
                self.instructions.next = executor.state.frames[-1].current
            self.instructions.suspended = [frame.current for frame in executor.state.frames[-2::-1]]
            self.instructions.update()

            self.call_stack.update()
            self.console.update()

            if returned:
                if isinstance(value, BaseException):
                    self.page.show_dialog(ErrorDialog(self.page, value))
                else:
                    self.page.show_dialog(ReturnDialog(self.page, value))
                self.result.set_result(value)
                return

            await self.send.put(self.state.delay)

    def create_task[**P, T](
        self, coroutine: Callable[P, CoroutineType[Any, Any, T]], /, *args: P.args, **kwargs: P.kwargs
    ) -> Future[T] | None:
        if self.closing:
            return None

        future = self.page.run_task(coroutine, *args, **kwargs)
        self.tasks.add(future)
        future.add_done_callback(self.tasks.discard)

        return future


def execute(machine: StackMachine, *args: None | int | bool | str, seed: int | str | Random | None = None):
    result: Future[Any] = Future()
    ft.run(partial(App, machine, args=args, seed=seed, result=result))
    return result.result()
