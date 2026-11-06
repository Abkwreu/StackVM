from __future__ import annotations

import io
import itertools as it
import sys
import time
from collections import deque
from collections.abc import Callable, Generator
from contextlib import contextmanager
from pathlib import Path
from random import Random
from types import NoneType
from typing import Any, BinaryIO, Literal, Self, TextIO, assert_never, cast

from stackvm._util import (
    FILE_MODES,
    TYPES,
    InstructedError,
    Instruction,
    OpCode,
    PopPeek,
    ResolvedInstruction,
    StackItem,
    StackUnderflowError,
    VMFrame,
    VMState,
    unzigzag,
)

if sys.version_info < (3, 15):
    from stackvm._util import sentinel


def process_instruction(
    state: VMState,
    instructions: tuple[ResolvedInstruction, ...],
    push: Callable[[list[Any], Any], None],
    pop: PopPeek,
    peek: PopPeek,
    rng: Random,
    stdin: Callable[[], str],
    stdout: TextIO,
) -> tuple[bool, Any]:
    frame = state.frames[-1]
    current, stack, env, prev = frame.current, frame.stack, frame.env, frame.prev

    if current >= len(instructions):
        return True, None

    value: Any
    returned, value, to = False, None, current + 1

    instr = instructions[current]
    opcode, arg, arg2 = instr.opcode, instr.arg, instr.arg2
    try:
        match opcode:
            case OpCode.NOOP:
                pass

            case OpCode.NONE:
                push(stack, None)
            case OpCode.INT:
                push(stack, arg)
            case OpCode.CHR:
                if arg == -1:
                    push(stack, "")
                else:
                    push(stack, chr(arg))
            case OpCode.BOOL:
                push(stack, bool(arg))

            case OpCode.TO_INT:
                push(stack, int(pop(stack)))
            case OpCode.TO_FLOAT:
                push(stack, float(pop(stack)))
            case OpCode.TO_CHR:
                push(stack, chr(pop(stack)))
            case OpCode.TO_STR:
                push(stack, str(pop(stack)))
            case OpCode.TO_BOOL:
                push(stack, bool(pop(stack)))
            case OpCode.TO_BYTES:
                push(stack, bytes(pop(stack)))

            case OpCode.ORD:
                push(stack, ord(pop(stack)))
            case OpCode.SLICE:
                step, stop, start = (pop(stack), pop(stack), pop(stack))
                push(stack, slice(start, stop, step))
            case OpCode.TYPE:
                obj = pop(stack)
                for index, cls in enumerate(TYPES):
                    if isinstance(obj, cls):
                        push(stack, index)
                        break
                else:
                    raise RuntimeError(f"Unrecognized type {type(obj).__name__}")

            case OpCode.LOAD:
                try:
                    push(stack, env[arg])
                except KeyError:
                    raise UnboundLocalError(f"Variable {arg} is unbound") from None
            case OpCode.STORE:
                frame.store(arg, pop(stack))
            case OpCode.GLOBAL:
                if arg in env.maps[0]:
                    # perhaps odd, but this is what Python raises when you use a global before the global keyword
                    raise SyntaxError(f"Variable {arg} was already assigned as a local variable when declared global")
                frame.global_vars.add(arg)

            case OpCode.COPY:
                item = peek(stack, -(arg + 1) if arg < 0 else -arg)
                push(stack, item)
            case OpCode.SWAP:
                loc = -(arg + 1) if arg < 0 else -arg
                try:
                    stack[loc], stack[-1] = stack[-1], stack[loc]
                except IndexError:
                    raise StackUnderflowError
            case OpCode.ROLL:
                try:
                    item = stack.pop(-(arg + 1) if arg < 0 else -arg)
                except IndexError:
                    raise StackUnderflowError
                stack.append(item)
            case OpCode.POP:
                pop(stack)

            case OpCode.ADD:
                addend, augend = pop(stack), pop(stack)
                push(stack, augend + addend)
            case OpCode.SUB:
                subtrahend, minuend = pop(stack), pop(stack)
                push(stack, minuend - subtrahend)
            case OpCode.MUL:
                multiplier, multiplicand = pop(stack), pop(stack)
                push(stack, multiplicand * multiplier)
            case OpCode.DIV:
                divisor, dividend = pop(stack), pop(stack)
                push(stack, dividend / divisor)
            case OpCode.FLOORDIV:
                divisor, dividend = pop(stack), pop(stack)
                push(stack, dividend // divisor)
            case OpCode.MOD:
                divisor, dividend = pop(stack), pop(stack)
                if isinstance(dividend, str) and isinstance(divisor, list):
                    # deliberate choice to make string formatting possible without adding tuples or a format instruction
                    divisor = tuple(divisor)
                push(stack, dividend % divisor)
            case OpCode.POW:
                exponent, base = pop(stack), pop(stack)
                if (
                    isinstance(base, (int | float))
                    and base < 0
                    and isinstance(exponent, float)
                    and not exponent.is_integer()
                ):
                    raise ArithmeticError("Cannot raise a negative number to a non-integral power")
                push(stack, base**exponent)
            case OpCode.AND:
                right, left = pop(stack), pop(stack)
                push(stack, left & right)
            case OpCode.OR:
                right, left = pop(stack), pop(stack)
                push(stack, left | right)
            case OpCode.XOR:
                right, left = pop(stack), pop(stack)
                push(stack, left ^ right)
            case OpCode.LSHIFT:
                right, left = pop(stack), pop(stack)
                push(stack, left << right)
            case OpCode.RSHIFT:
                right, left = pop(stack), pop(stack)
                push(stack, left >> right)

            case OpCode.INVERT:
                push(stack, ~pop(stack))
            case OpCode.NEG:
                push(stack, -pop(stack))
            case OpCode.ABS:
                push(stack, abs(pop(stack)))
            case OpCode.NOT:
                push(stack, not pop(stack))

            case OpCode.EQ:
                right, left = pop(stack), pop(stack)
                push(stack, left == right)
            case OpCode.NE:
                right, left = pop(stack), pop(stack)
                push(stack, left != right)
            case OpCode.LT:
                right, left = pop(stack), pop(stack)
                push(stack, left < right)
            case OpCode.GT:
                right, left = pop(stack), pop(stack)
                push(stack, left > right)
            case OpCode.LE:
                right, left = pop(stack), pop(stack)
                push(stack, left <= right)
            case OpCode.GE:
                right, left = pop(stack), pop(stack)
                push(stack, left >= right)
            case OpCode.IS:
                right, left = pop(stack), pop(stack)
                push(stack, left is right)
            case OpCode.IS_NOT:
                right, left = pop(stack), pop(stack)
                push(stack, left is not right)
            case OpCode.CONTAINS:
                push(stack, pop(stack) in pop(stack))
            case OpCode.IS_TYPE:
                val = pop(stack)
                cls = TYPES[arg]
                if cls is bool:
                    push(stack, type(val) is cls)
                else:
                    push(stack, isinstance(val, cls))

            case OpCode.LIST:
                items = deque()
                for _ in range(arg):
                    items.appendleft(pop(stack))
                push(stack, list(items))
            case OpCode.DICT:
                items = deque()
                for _ in range(arg):
                    value, key = pop(stack), pop(stack)
                    items.appendleft((key, value))
                push(stack, dict(items))
            case OpCode.LEN:
                push(stack, len(peek(stack)))
            case OpCode.APPEND:
                item, obj = (pop(stack), peek(stack))
                obj.append(item)
            case OpCode.KEYS:
                push(stack, list(peek(stack).keys()))

            case OpCode.GETITEM:
                index, obj = (pop(stack), peek(stack))
                push(stack, obj[index])
            case OpCode.SETITEM:
                value, index, obj = (pop(stack), pop(stack), peek(stack))
                obj[index] = value
            case OpCode.DELITEM:
                index, obj = (pop(stack), peek(stack))
                del obj[index]

            case OpCode.JUMP:
                to = arg
            case OpCode.JUMP_FALSE:
                if not pop(stack):
                    to = arg
            case OpCode.JUMP_TRUE:
                if pop(stack):
                    to = arg
            case OpCode.JUMP_INDIRECT:
                target = pop(stack)
                if target < 0:
                    raise ValueError("Cannot jump to a negative index")
                to = target

            case OpCode.CALL:
                if len(stack) < arg2:
                    raise StackUnderflowError

                if arg2:
                    call_args = stack[-arg2:]
                    del stack[-arg2:]
                else:
                    call_args = []

                state.frames.append(VMFrame(current=arg, stack=call_args, prev=current, globals_=env.maps[1]))

            case OpCode.CALL_INDIRECT:
                target = pop(stack)
                if target < 0:
                    raise ValueError("Cannot jump to a negative index")

                if len(stack) < arg2:
                    raise StackUnderflowError

                if arg2:
                    call_args = stack[-arg2:]
                    del stack[-arg2:]
                else:
                    call_args = []

                state.frames.append(VMFrame(current=target, stack=call_args, prev=current, globals_=env.maps[1]))

            case OpCode.NOW:
                push(stack, time.time())
            case OpCode.OFTEN:
                push(stack, rng.random() < 3 / 4)
            case OpCode.SELDOM:
                push(stack, rng.random() < 1 / 6)

            case OpCode.INPUT:
                push(stack, stdin())
            case OpCode.PRINT:
                print(pop(stack), file=stdout)

            case OpCode.OPEN:
                push(stack, open(pop(stack), FILE_MODES[arg]))  # noqa: SIM115
            case OpCode.READ:
                push(stack, peek(stack).read(arg))
            case OpCode.WRITE:
                content, file = (pop(stack), peek(stack))
                file.write(content)
            case OpCode.CLOSE:
                pop(stack).close()

            case OpCode.SIZE:
                push(stack, len(stack))
            case OpCode.LOCATE:
                push(stack, current)

            # terminal operations don't require an item on the stack
            case OpCode.ERROR:
                try:
                    raise InstructedError(pop(stack))
                except StackUnderflowError:
                    raise InstructedError
            case OpCode.RETURN:
                returned = True
                try:
                    value = stack[-1]
                except StackUnderflowError:
                    pass

            case OpCode.SHOW:
                title = f"Stack at Instruction {current}"
                print("-" * len(title), file=stdout)
                print(title, file=stdout)
                print(f"(Instruction: {None if prev is None else instructions[prev]})", file=stdout)
                print("-" * len(title), file=stdout)

                for index in range(len(stack) - 1, -1, -1):
                    value = peek(stack, index)
                    print(f"{len(stack) - index}: {value!r}", file=stdout)

            case _:
                assert_never(opcode)
                raise NotImplementedError(f"Unknown opcode: {instr.opcode}")
    except StackUnderflowError:
        raise StackUnderflowError(f"Stack underflow at instruction {current}: {instructions[current]}") from None

    frame.current = to
    frame.prev = current
    return returned, value


class Executor:
    instructions: tuple[ResolvedInstruction, ...]
    args: tuple[Any, ...]
    call: bool
    rng: Random
    push: Callable[[list[Any], Any], None]
    pop: PopPeek
    peek: PopPeek
    stdin: Callable[[], str]
    stdout: TextIO
    state: VMState
    done: bool

    def __init__(
        self,
        instructions: tuple[ResolvedInstruction, ...],
        *args: None | int | str | bool,
        seed: int | str | Random | None = None,
        push: Callable[[list[Any], Any], None],
        pop: PopPeek,
        peek: PopPeek,
        stdin: Callable[[], str],
        stdout: TextIO,
    ) -> None:
        self.instructions = instructions
        self.args = args
        self.rng = seed if isinstance(seed, Random) else Random(seed)
        self.push = push
        self.pop = pop
        self.peek = peek
        self.stdin = stdin
        self.stdout = stdout
        self.state = VMState()
        self.done = False

        for arg in self.args:
            push(self.state.frames[-1].stack, arg)

    def __call__(self) -> Any:
        if self.done:
            raise RuntimeError("Executor has already returned")

        returned, value = False, None
        while not returned:
            returned, value = self.step()
        self.done = True
        return value

    def step(self) -> tuple[Literal[True], Any] | tuple[Literal[False], None]:
        if self.done:
            raise RuntimeError("Executor has already returned")

        returned, value = process_instruction(
            self.state, self.instructions, self.push, self.pop, self.peek, self.rng, self.stdin, self.stdout
        )

        if returned:
            self.state.frames.pop()

            try:
                frame = self.state.frames[-1]
            except IndexError:
                self.done = True
                return True, self.peek([value])

            frame.stack.append(value)

        return False, None


class StackMachine:
    __slots__ = ("_forward_refs", "_instructions", "_sealed", "_used_vars")

    _instructions: list[Instruction]
    _sealed: bool
    _used_vars: set[int]
    _forward_refs: dict[sentinel, int]

    def __init__(self) -> None:
        self._instructions = []
        self._sealed = False
        self._used_vars = set()
        self._forward_refs = {}

    def __call__(self, *args: None | int | str | bool, seed: int | str | Random | None = None) -> Any:
        """
        Executes the defined program.

        :param args: The initial arguments to pass into the program.
        These will be present on the stack at the start of the program, with the first supplied argument at the bottom.
        :param seed: The random seed or `Random` instance used for the `OFTEN` and `SELDOM` instructions.
        :return: The value returned by the program.
        """
        executor = self.executor(*args, seed=seed)
        return executor()

    def __bytes__(self) -> bytes:
        result = bytearray()
        for instr in self.instructions:
            result.extend(bytes(instr))
        return bytes(result)

    def executor(
        self,
        *args: None | int | str | bool,
        seed: int | str | Random | None = None,
        push: Callable[[list[Any], Any], None] | None = None,
        pop: PopPeek | None = None,
        peek: PopPeek | None = None,
    ) -> Executor:
        if push is None:

            def default_push(stack: list[Any], obj: Any) -> None:
                stack.append(obj)

            push = default_push

        if pop is None:

            def default_pop(stack: list[Any], index: int = -1) -> Any:
                try:
                    return stack.pop(index)
                except IndexError:
                    raise StackUnderflowError from None

            pop = default_pop

        if peek is None:

            def default_peek(stack: list[Any], index: int = -1) -> Any:
                try:
                    return stack[index]
                except IndexError:
                    raise StackUnderflowError from None

            peek = default_peek

        instructions = tuple(self._instructions)
        if not self._sealed and any(isinstance(instr.arg, sentinel) for instr in instructions):
            raise RuntimeError("Unbound forward reference found in instructions")
        instructions = cast(tuple[ResolvedInstruction, ...], instructions)

        if not all(isinstance(arg, NoneType | int) or isinstance(arg, str) and len(arg) <= 1 for arg in args):
            raise TypeError("Only arguments of None, int, bool, or chr are permitted")

        return Executor(instructions, *args, seed=seed, push=push, pop=pop, peek=peek, stdin=input, stdout=sys.stdout)

    def ui_executor(
        self,
        *args: None | int | str | bool,
        seed: int | str | Random | None = None,
        stdin: Callable[[], str] = input,
        stdout: TextIO = sys.stdout,
    ) -> Executor:
        instructions = tuple(self._instructions)
        if not self._sealed and any(isinstance(instr.arg, sentinel) for instr in instructions):
            raise RuntimeError("Unbound forward reference found in instructions")
        instructions = cast(tuple[ResolvedInstruction, ...], instructions)

        if not all(isinstance(arg, NoneType | int) or isinstance(arg, str) and len(arg) <= 1 for arg in args):
            raise TypeError("Only arguments of None, int, bool, or chr are permitted")

        def push(stack: list[Any], obj: Any) -> None:
            stack.append(StackItem(obj))

        def pop(stack: list[StackItem], index: int = -1) -> Any:
            try:
                return stack.pop(index).obj
            except IndexError:
                raise StackUnderflowError from None

        def peek(stack: list[StackItem], index: int = -1) -> Any:
            try:
                return stack[index].obj
            except IndexError:
                raise StackUnderflowError from None

        return Executor(
            instructions,
            *args,
            seed=seed,
            push=push,
            pop=pop,
            peek=peek,
            stdin=stdin,
            stdout=stdout,
        )

    def ui(self, *args: None | int | bool | str, seed: int | str | Random | None = None) -> Any:
        """
        Executes the program in the interactive UI powered by Flet.

        :param args: The initial arguments to pass into the program.
        These will be present on the stack at the start of the program, with the first supplied argument at the bottom.
        :param seed: The random seed or `Random` instance used for the `OFTEN` and `SELDOM` instructions.
        :return: The value returned by the program.
        """
        from stackvm._ui import execute

        return execute(self, *args, seed=seed)

    def dump_file(self, path: str | Path | BinaryIO) -> None:
        if isinstance(path, str):
            path = Path(path)

        if isinstance(path, Path):
            path.write_bytes(bytes(self))
            return

        path.write(bytes(self))

    @classmethod
    def load_file(cls, path: str | Path | BinaryIO) -> Self:
        if isinstance(path, str):
            path = Path(path)

        if isinstance(path, Path):
            data = path.read_bytes()
            return cls.from_bytes(data)

        data = path.read()
        return cls.from_bytes(data)

    @classmethod
    def from_bytes(cls, data: bytes | bytearray) -> Self:
        if len(data) % 2 == 1:
            raise ValueError("Cannot load an odd number of bytes")

        instructions: list[Instruction] = []

        used_vars: set[int] = set()

        current: int = 0
        for chunk in it.batched(data, 2):
            opcode_value, arg = chunk
            current += arg

            if opcode_value == 255:
                current <<= 8
                continue

            arg = unzigzag(current)

            opcode = OpCode(opcode_value)
            if opcode.args == 2:
                arg, arg2 = arg >> 4, arg & 15
                instructions.append(Instruction(opcode, arg, arg2))
            else:
                instructions.append(Instruction(opcode, arg))

            if opcode in {OpCode.LOAD, OpCode.STORE, OpCode.GLOBAL}:
                used_vars.add(arg)

            current = 0

        self = cls()
        self._instructions = instructions
        self._used_vars = used_vars
        self._sealed = True

        return self

    def __enter__(self) -> Self:
        return self

    def __exit__(self, *args):
        if any(isinstance(instr.arg, sentinel) for instr in self._instructions):
            raise RuntimeError("Unresolved forward reference found in stack machine definition")
        self._sealed = True

    @property
    def instructions(self) -> tuple[Instruction, ...]:
        return tuple(self._instructions)

    def dis(self) -> str:
        result = io.StringIO()

        jump_targets = set()
        jump_opcodes = {OpCode.JUMP, OpCode.JUMP_TRUE, OpCode.JUMP_FALSE, OpCode.CALL}
        for i, instr in enumerate(self._instructions):
            if instr.opcode in jump_opcodes and isinstance(instr.arg, int):
                jump_targets.add(instr.arg)

        labels = {target: i for i, target in enumerate(sorted(jump_targets))}
        label_width = 0 if not labels else len(str(len(labels))) + 2

        digits = len(str(len(self._instructions) - 1))

        print("-------------------------", file=result)
        print("STACK MACHINE DISASSEMBLY", file=result)
        print("-------------------------", file=result)

        for i, instr in enumerate(self._instructions):
            if label_width:
                if i in labels:
                    print(f"{'L' + str(labels[i]) + ':':>{label_width}} ", file=result, end="")
                else:
                    print(" " * (label_width + 1), file=result, end="")

            print(f"{i:0{digits}d}   {instr.opcode.name:<12} {instr.arg}", file=result, end="")

            if instr.has_second_arg():
                print(f" {instr.arg2}", file=result, end="")

            if instr.opcode in jump_opcodes and not isinstance(instr.arg, sentinel):
                try:
                    print(f" (L{labels[instr.arg]})", file=result)
                except KeyError:
                    print(file=result)
            else:
                print(file=result)

        return result.getvalue()

    def _instr(self, opcode: OpCode, arg: int | sentinel = 0, arg2: int = 0) -> None:
        if self._sealed:
            raise RuntimeError("Stack machine definition has been finalized")
        self._instructions.append(Instruction(opcode, arg, arg2))

    def noop(self) -> Self:
        """This instruction does nothing when the program is executed."""
        self._instr(OpCode.NOOP)
        return self

    def const(self, *values: None | int | bool | str) -> Self:
        """
        Pushes a constant to the stack.
        Permitted constants are those of type `None`, `int`, `bool`, as well as strings of length 0 or 1.
        """
        for value in values:
            if value is None:
                self._instr(OpCode.NONE)
            elif type(value) is bool:
                self._instr(OpCode.BOOL, int(value))
            elif type(value) is int:
                self._instr(OpCode.INT, value)
            elif type(value) is str and len(value) <= 1:
                self._instr(OpCode.CHR, ord(value) if value else -1)
            else:
                raise TypeError(f"Disallowed constant {value!r}")
        return self

    def int(self) -> Self:
        """Calls `int()` on the topmost value on the stack."""
        self._instr(OpCode.TO_INT)
        return self

    def float(self) -> Self:
        """Calls `float()` on the topmost value on the stack."""
        self._instr(OpCode.TO_FLOAT)
        return self

    def chr(self) -> Self:
        """Calls `chr()` on the topmost value on the stack."""
        self._instr(OpCode.TO_CHR)
        return self

    def str(self) -> Self:
        """Calls `str()` on the topmost value on the stack."""
        self._instr(OpCode.TO_STR)
        return self

    def bool(self) -> Self:
        """Calls `bool()` on the topmost value on the stack."""
        self._instr(OpCode.TO_BOOL)
        return self

    def bytes(self) -> Self:
        """Calls `bytes()` on the topmost value on the stack."""
        self._instr(OpCode.TO_BYTES)
        return self

    def ord(self) -> Self:
        """Calls `ord()` on the topmost value on the stack."""
        self._instr(OpCode.ORD)
        return self

    def slice(self) -> Self:
        """
        Pops the three topmost items from the stack, and pushes `slice(third, second, top)` to the stack.
        """
        self._instr(OpCode.SLICE)
        return self

    def type(self) -> Self:
        """
        Replaces the on top of the stack with an integer representing its type, according to the following:

        * `None`: 0
        * `bool`: 1
        * `int`: 2
        * `float`: 3
        * `str`: 4
        * `bytes`: 5
        * `slice`: 6
        * `list`: 7
        * `dict`: 8
        * File (`IOBase`): 9
        """
        self._instr(OpCode.TYPE)
        return self

    def new_var(self) -> int:
        """
        Allocates a new variable, guaranteed to use a variable ID that has not been used yet.

        :return: The ID of the allocated variable.
        """
        for i in it.count():
            if i not in self._used_vars:
                self._used_vars.add(i)
                return i
        assert False

    def new_global(self) -> int:
        """
        Allocates a new variable, guaranteed to use a variable ID that has not been used yet.
        This new variable is set to be global in the current frame.

        :return: The ID of the allocated variable.
        """
        for i in it.count():
            if i not in self._used_vars:
                self._used_vars.add(i)
                self.global_var(i)
                return i
        assert False

    def load(self, *ids: int) -> Self:
        """
        Loads the variable assigned to the given ID, pushing it onto the stack.
        If multiple IDs are given, they will all be pushed onto the stack in order.

        :param ids: The IDs of the variables to load.
        It is recommended that these are values returned by `new_var()` or `new_global()`, to avoid conflicts.
        """
        for var in ids:
            self._used_vars.add(var)
            self._instr(OpCode.LOAD, var)
        return self

    def store(self, *ids: int) -> Self:
        """
        Stores the topmost value on the stack to the variable with the given ID.
        If multiple IDs are given, the topmost value on the stack will be assigned to the first supplied ID,
        the next value on the stack will be assigned to the second supplied ID, and so on.

        :param ids: The IDs of the variables to store.
        It is recommended that these are values returned by `new_var()` or `new_global()`, to avoid conflicts.
        """
        for var in ids:
            self._used_vars.add(var)
            self._instr(OpCode.STORE, var)
        return self

    def global_var(self, *ids: int) -> Self:
        """
        Marks the variable(s) with the given ID(s) as global in the current frame.

        :param ids: The IDs of the variables to set as global.
        It is recommended that these are values returned by `new_var()` or `new_global()`, to avoid conflicts.
        """
        for var in ids:
            self._used_vars.add(var)
            self._instr(OpCode.GLOBAL, var)
        return self

    def copy(self, *depths: int) -> Self:
        """
        Pushes a copy of a value in the stack to the top of the stack.

        The stack is 1-indexed, so 1 indicates the top item, 2 indicates the second item from top, and so on.
        Negative indices are relative to the bottom of the stack, so -1 indicates the bottom item, etc.

        If multiple depths are specified, all positive ones following the first will be adjusted
        to account for the items pushed onto the stack by the previous copy instructions.
        Therefore, `.copy(1, 2, 3)` is equivalent to `.copy(1).copy(3).copy(5)`.

        :param depths: The 1-indexed locations of values from the stack to copy.
        If not supplied, defaults to `(1,)`, copying the topmost value on the stack.
        """
        if not depths:
            depths = (1,)

        for i, depth in enumerate(depths):
            if depth == 0:
                raise TypeError("Copy depth cannot be 0")
            if depth < 0:
                self._instr(OpCode.COPY, depth)
            else:
                self._instr(OpCode.COPY, depth + i)
        return self

    def swap(self, depth: int = 2) -> Self:
        """
        Swaps the value at the given index with the topmost value on the stack.

        The stack is 1-indexed, so 1 indicates the top item, 2 indicates the second item from top, and so on.
        Negative indices are relative to the bottom of the stack, so -1 indicates the bottom item, etc.

        :param depth: The 1-indexed location of value from the stack to swap with.
        If not supplied, defaults to `2`, swapping the two topmost values on the stack.
        """
        if depth == 0:
            raise TypeError("Swap depth cannot be 0")
        self._instr(OpCode.SWAP, depth)
        return self

    def roll(self, depth: int = 3) -> Self:
        """
        Moves the value at the given index to the top of the stack, shifting intervening items down one position.

        The stack is 1-indexed, so 1 indicates the top item, 2 indicates the second item from top, and so on.
        Negative indices are relative to the bottom of the stack, so -1 indicates the bottom item, etc.

        :param depth: The 1-indexed location of value from the stack to swap with. If not supplied, defaults to `3`,
        moving the third item on the stack to the top, while shifting the two topmost items down one position.
        """
        if depth == 0:
            raise TypeError("Roll depth cannot be 0")
        self._instr(OpCode.ROLL, depth)
        return self

    def pop(self, times: int = 1) -> Self:
        """
        Pops the topmost item on the stack.

        :param times: How many items to pop from the stack. Defaults to 1.
        """
        for _ in range(times):
            self._instr(OpCode.POP)
        return self

    def add(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second + top` to the stack.
        """
        self._instr(OpCode.ADD)
        return self

    def sub(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second - top` to the stack.
        """
        self._instr(OpCode.SUB)
        return self

    def mul(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second * top` to the stack.
        """
        self._instr(OpCode.MUL)
        return self

    def div(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second / top` to the stack.
        """
        self._instr(OpCode.DIV)
        return self

    def floordiv(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second // top` to the stack.
        """
        self._instr(OpCode.FLOORDIV)
        return self

    def mod(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second % top` to the stack.

        Uniquely, if `second` is of type `str` and `top` is of type `list`,
        `top` is converted to `tuple` before executing this instruction.
        This will perform %-style string formatting.
        """
        self._instr(OpCode.MOD)
        return self

    def pow(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second ** top` to the stack.
        """
        self._instr(OpCode.POW)
        return self

    def band(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second & top` to the stack.
        """
        self._instr(OpCode.AND)
        return self

    def bor(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second | top` to the stack.
        """
        self._instr(OpCode.OR)
        return self

    def xor(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second ^ top` to the stack.
        """
        self._instr(OpCode.XOR)
        return self

    def lshift(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second << top` to the stack.
        """
        self._instr(OpCode.LSHIFT)
        return self

    def rshift(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second >> top` to the stack.
        """
        self._instr(OpCode.RSHIFT)
        return self

    def invert(self) -> Self:
        """
        Inverts (`~`) the topmost item on the stack.
        """
        self._instr(OpCode.INVERT)
        return self

    def neg(self) -> Self:
        """
        Negates (`-`) the topmost item on the stack.
        """
        self._instr(OpCode.NEG)
        return self

    def abs(self) -> Self:
        """
        Calls `abs()` on the topmost item on the stack.
        """
        self._instr(OpCode.ABS)
        return self

    def lnot(self) -> Self:
        """
        Pops the topmost item on the stack, and pushes `not top` to the stack.
        """
        self._instr(OpCode.NOT)
        return self

    def eq(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second == top` to the stack.
        """
        self._instr(OpCode.EQ)
        return self

    def ne(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second != top` to the stack.
        """
        self._instr(OpCode.NE)
        return self

    def lt(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second < top` to the stack.
        """
        self._instr(OpCode.LT)
        return self

    def gt(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second > top` to the stack.
        """
        self._instr(OpCode.GT)
        return self

    def le(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second <= top` to the stack.
        """
        self._instr(OpCode.LE)
        return self

    def ge(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second >= top` to the stack.
        """
        self._instr(OpCode.GE)
        return self

    def ident(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second is top` to the stack.
        """
        self._instr(OpCode.IS)
        return self

    def is_not(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `second is not top` to the stack.
        """
        self._instr(OpCode.IS_NOT)
        return self

    def contains(self) -> Self:
        """
        Pops the two topmost items from the stack and pushes `top in second` to the stack.
        Note the differing order of the operands in contrast to the rest of the binary operations.
        """
        self._instr(OpCode.CONTAINS)
        return self

    def is_type(self, cls: None | type) -> Self:
        """
        Pops the topmost item on the stack, and pushes True only if it is of the specified type.

        :param cls: The type to check the item against.
        Can be `None`, `NoneType`, `bool`, `int`, `float`, `str`, `bytes`, `slice`, `list`, `dict`, or `IOBase`.
        """
        try:
            self._instr(OpCode.IS_TYPE, TYPES.index(NoneType if cls is None else cls))
        except ValueError:
            assert cls is not None
            raise ValueError(f"Type {cls.__name__} is unobtainable") from None
        return self

    def list(self, length: int = 0) -> Self:
        """
        Pops the top `length` items off the stack, collecting them into a list which is then pushed onto the stack.
        The topmost item on the stack becomes the last item in the list.

        :param length: The size of the list to create. 0 by default, creating an empty list.
        """
        if length < 0:
            raise ValueError("List size cannot be negative")
        self._instr(OpCode.LIST, length)
        return self

    def dict(self, length: int = 0) -> Self:
        """
        Pushes a dictionary of size `length` onto the stack, collecting the topmost items on the stack.
        The topmost item will become the value of the last item in the dictionary,
        and the item below that will be the last key in the dictionary, and so on.

        :param length: The size of the dictionary to create. 0 by default, creating an empty default.
        """
        if length < 0:
            raise ValueError("Dictionary size cannot be negative")
        self._instr(OpCode.DICT, length)
        return self

    def len(self) -> Self:
        """
        Pushes the length of the topmost item to the stack.
        """
        self._instr(OpCode.LEN)
        return self

    def append(self) -> Self:
        """
        Pops the topmost item on the stack and calls `second.append(top)`.
        """
        self._instr(OpCode.APPEND)
        return self

    def keys(self) -> Self:
        """
        Pushes a list containing the keys of the dictionary on top of the stack.
        """
        self._instr(OpCode.KEYS)
        return self

    def getitem(self) -> Self:
        """
        Pops the top item from the stack, and pushes `second[top]` to the stack.
        """
        self._instr(OpCode.GETITEM)
        return self

    def setitem(self) -> Self:
        """
        Pops the two topmost items from the stack, and calls `third[second] = top`.
        """
        self._instr(OpCode.SETITEM)
        return self

    def delitem(self) -> Self:
        """
        Pops the topmost item on the stack, and calls `del second[top]`.
        """
        self._instr(OpCode.DELITEM)
        return self

    def forward(self) -> sentinel:
        """
        Creates a forward reference, which can be passed into jump and call instructions.

        The forward reference can later be bound using `label()`.

        :return: A forward reference object that can be used as a jump target or later bound.
        """
        return sentinel("FORWARD")

    def jump(self, target: int | sentinel) -> Self:
        """
        Jumps to just before the instruction indicated by the target location.

        If `target` is a sentinel, it will be replaced with the appropriate location when it is bound.

        :param target: The location of the instruction or the forward reference to jump to.
        """
        if isinstance(target, sentinel) and target in self._forward_refs:
            target = self._forward_refs[target]

        if isinstance(target, int) and target < 0:
            raise ValueError("Jump destination cannot be negative")

        self._instr(OpCode.JUMP, target)
        return self

    def jump_false(self, target: int | sentinel) -> Self:
        """
        Pops the topmost item on the stack,
        and jumps to just before the instruction indicated by the target location if it is falsy.

        If `target` is a sentinel, it will be replaced with the appropriate location when it is bound.

        :param target: The location of the instruction or the forward reference to jump to.
        """
        if isinstance(target, sentinel) and target in self._forward_refs:
            target = self._forward_refs[target]

        if isinstance(target, int) and target < 0:
            raise ValueError("Jump destination cannot be negative")

        self._instr(OpCode.JUMP_FALSE, target)
        return self

    def jump_true(self, target: int | sentinel) -> Self:
        """
        Pops the topmost item on the stack,
        and jumps to just before the instruction indicated by the target location if it is truthy.

        If `target` is a sentinel, it will be replaced with the appropriate location when it is bound.

        :param target: The location of the instruction or the forward reference to jump to.
        """
        if isinstance(target, sentinel) and target in self._forward_refs:
            target = self._forward_refs[target]

        if isinstance(target, int) and target < 0:
            raise ValueError("Jump destination cannot be negative")

        self._instr(OpCode.JUMP_TRUE, target)
        return self

    def jump_indirect(self) -> Self:
        """
        Pops the topmost item on the stack,
        and jumps to just before the instruction at the location indicated by the value of the popped item.
        """
        self._instr(OpCode.JUMP_INDIRECT)
        return self

    def call(self, target: int | sentinel, args: int = 0) -> Self:
        """
        Creates a new frame that starts with its instruction pointer at the instruction with location `target`.

        This frame is given a separate operand stack, with only the top `args` items
        of the current stack, popped and passed in as arguments.

        The frame has its own set of local variables, though it inherits any global variables from the current frame.
        However, if these global variables are then assigned in the new frame, they will be local unless redeclared as global there.

        When a `RETURN` instruction is executed in the new frame, that frame will be discarded
        and the return value will be pushed onto the stack of the previous frame.

        :param target: The location of the instruction or forward reference to start the new frame at.
        :param args: The number of arguments to pass to the new frame. Defaults to 0.
        """
        if isinstance(target, sentinel) and target in self._forward_refs:
            target = self._forward_refs[target]

        if isinstance(target, int) and target < 0:
            raise ValueError("Call target cannot be negative")

        self._instr(OpCode.CALL, target, args)
        return self

    def call_indirect(self, args: int = 0) -> Self:
        """
        Pops the topmost item of the stack, and creates a new frame that starts
        with its instruction pointer at the location indicated by the value of the popped item.

        This frame is given a separate operand stack, with only the top `args` items
        of the current stack, popped and passed in as arguments.

        The frame has its own set of local variables, though it inherits any global variables from the current frame.
        However, if these global variables are then assigned in the new frame, they will be local unless redeclared as global there.

        When a `RETURN` instruction is executed in the new frame, that frame will be discarded
        and the return value will be pushed onto the stack of the previous frame.

        :param target: The location of the instruction or forward reference to start the new frame at.
        :param args: The number of arguments to pass to the new frame. Defaults to 0.
        """
        self._instr(OpCode.CALL_INDIRECT, 0, args)
        return self

    def label(self, forward: sentinel | None = None) -> int:
        """
        Returns the index of the next instruction, used for creating labels for `.jump()` and `.call()`.

        If a forward reference is passed, it will also bind that forward reference here.

        :param forward: The forward reference to bind, if any
        """
        loc = len(self._instructions)

        if isinstance(forward, sentinel):
            if forward in self._forward_refs:
                raise ValueError("Forward reference has already been bound")

            self._forward_refs[forward] = loc
            for index, instr in enumerate(self._instructions):
                if instr.arg is forward:
                    self._instructions[index] = Instruction(instr.opcode, loc, instr.arg2)

        return loc

    @contextmanager
    def block(
        self, start: sentinel | None = None, stop: sentinel | None = None
    ) -> Generator[tuple[int, sentinel], None, None]:
        """
        Returns a label and a forward reference, bound to the start and end of the block, respectively.

        If a forward reference sentinel is passed into `start` or `stop`,
        those will be bound instead of creating a new label or a new forward reference.
        """
        if stop is None:
            stop = self.forward()
        yield self.label(start) if isinstance(start, sentinel) else self.label(), stop
        self.label(stop)

    def now(self) -> Self:
        """
        Pushes the current time in seconds since the UNIX epoch onto the stack.
        """
        self._instr(OpCode.NOW)
        return self

    def often(self) -> Self:
        """
        Pushes `True` onto the stack with 3/4 probability and `False` with 1/4 probability.
        """
        self._instr(OpCode.OFTEN)
        return self

    def seldom(self) -> Self:
        """
        Pushes `True` onto the stack with 1/6 probability and `False` with 5/6 probability.
        """
        self._instr(OpCode.SELDOM)
        return self

    def input(self) -> Self:
        """
        Reads a line from standard input and pushes it onto the stack.
        """
        self._instr(OpCode.INPUT)
        return self

    def print(self) -> Self:
        """
        Writes the topmost item on the stack to standard output.
        """
        self._instr(OpCode.PRINT)
        return self

    def open(self, mode: str = "r") -> Self:
        """
        Pops the topmost item on the stack, and opens the file indicated by its value, taken as a file path.

        :param mode: The mode to open the file with, as passed into `open()`. Defaults to `r`.
        """
        try:
            self._instr(OpCode.OPEN, FILE_MODES.index(mode))
        except ValueError:
            raise ValueError(f"Disallowed file mode {mode!r}") from None
        return self

    def read(self, length: int = -1) -> Self:
        """
        Reads `length` characters or bytes from file on top of the stack, pushing the result to the stack.

        :param length: The number of characters or bytes to read.
        If `-1` (as is default), reads all remaining contents of the file.
        """
        self._instr(OpCode.READ, length)
        return self

    def write(self) -> Self:
        """
        Pops the topmost item on the stack, and writes it to the file below it on the stack.
        """
        self._instr(OpCode.WRITE)
        return self

    def close(self) -> Self:
        """
        Pops the file on top of the stack and closes it.
        """
        self._instr(OpCode.CLOSE)
        return self

    def size(self) -> Self:
        """
        Pushes the current size of the operand stack onto the stack.
        The additional item pushed by this command is not included.
        """
        self._instr(OpCode.SIZE)
        return self

    def locate(self) -> Self:
        """
        Pushes the index of this instruction onto the stack.
        """
        self._instr(OpCode.LOCATE)
        return self

    def error(self) -> Self:
        """
        Raises an `InstructedError` when this instruction is executed.
        This will terminate the program, as this exception cannot be caught inside the virtual machine.

        If the stack is not empty, the topmost value on the stack will be used as the exception message.
        """
        self._instr(OpCode.ERROR)
        return self

    def ret(self) -> Self:
        """
        Returns the topmost value on the stack, or None if the stack is empty.
        """
        self._instr(OpCode.RETURN)
        return self

    def show(self) -> Self:
        """
        Prints the current operand stack to the console, intended for debugging.
        """
        self._instr(OpCode.SHOW)
        return self
