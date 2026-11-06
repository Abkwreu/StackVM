from __future__ import annotations

import sys
from collections import ChainMap
from collections.abc import Callable, MutableMapping
from dataclasses import InitVar, dataclass, field
from enum import Enum
from io import IOBase
from types import NoneType
from typing import TYPE_CHECKING, Any, Final, Protocol, Self

if sys.version_info < (3, 15):

    class sentinel:
        name: str

        def __init__(self, name: str) -> None:
            self.name = name

        def __repr__(self) -> str:
            return self.name


TYPES: Final[tuple[type, ...]] = (NoneType, bool, int, float, str, bytes, slice, list, dict, IOBase)
FILE_MODES: Final[tuple[str, ...]] = ("r", "w", "a", "r+", "w+", "a+", "rb", "wb", "ab", "rb+", "wb+", "ab+")


class OpCode(Enum):
    args: int
    _stack_effect: int | Callable[..., int]

    def __new__(cls, value: int, args: int, stack_effect: int | Callable[..., int]) -> Self:
        self = object.__new__(cls)
        self._value_ = value
        self.args = args
        self._stack_effect = stack_effect
        return self

    NOOP = (0, 0, 0)

    NONE = (1, 0, 1)
    INT = (2, 1, 1)
    CHR = (3, 1, 1)
    BOOL = (4, 1, 1)

    TO_INT = (8, 0, 0)
    TO_FLOAT = (9, 0, 0)
    TO_CHR = (10, 0, 0)
    TO_STR = (11, 0, 0)
    TO_BOOL = (12, 0, 0)
    TO_BYTES = (13, 0, 0)

    ORD = (16, 0, 0)
    SLICE = (17, 0, -2)
    TYPE = (18, 0, 0)

    LOAD = (20, 1, 1)
    STORE = (21, 1, -1)
    GLOBAL = (22, 1, 0)

    COPY = (24, 1, 1)
    SWAP = (25, 1, 0)
    ROLL = (26, 1, 0)
    POP = (27, 0, -1)

    ADD = (32, 0, -1)
    SUB = (33, 0, -1)
    MUL = (34, 0, -1)
    DIV = (35, 0, -1)
    FLOORDIV = (36, 0, -1)
    MOD = (37, 0, -1)
    POW = (38, 0, -1)
    AND = (39, 0, -1)
    OR = (40, 0, -1)
    INVERT = (41, 0, -1)
    XOR = (42, 0, -1)
    LSHIFT = (43, 0, -1)
    RSHIFT = (44, 0, -1)

    NEG = (48, 0, 0)
    ABS = (49, 0, 0)
    NOT = (50, 0, 0)

    EQ = (56, 0, -1)
    NE = (57, 0, -1)
    LT = (58, 0, -1)
    GT = (59, 0, -1)
    LE = (60, 0, -1)
    GE = (61, 0, -1)
    IS = (62, 0, -1)
    IS_NOT = (63, 0, -1)
    CONTAINS = (64, 0, -1)
    IS_TYPE = (65, 1, 0)

    LIST = (72, 1, lambda arg: -arg + 1)
    DICT = (73, 1, lambda arg: -(arg * 2) + 1)
    LEN = (74, 0, 1)
    APPEND = (75, 0, -1)
    KEYS = (76, 0, 1)

    GETITEM = (80, 0, 0)
    SETITEM = (81, 0, -2)
    DELITEM = (82, 0, -1)

    JUMP = (88, 1, 0)
    JUMP_FALSE = (89, 1, -1)
    JUMP_TRUE = (90, 1, -1)
    JUMP_INDIRECT = (91, 0, -1)

    CALL = (96, 2, lambda _, arg2: -arg2 + 1)
    CALL_INDIRECT = (97, 2, lambda _, arg2: -arg2)

    NOW = (104, 0, 1)
    OFTEN = (105, 0, 1)
    SELDOM = (106, 0, 1)

    INPUT = (112, 0, 1)
    PRINT = (113, 0, -1)

    OPEN = (120, 1, 0)
    READ = (121, 1, 1)
    WRITE = (122, 0, -1)
    CLOSE = (123, 0, -1)

    SIZE = (128, 0, 1)
    LOCATE = (129, 0, 1)

    ERROR = (240, 0, 0)
    RETURN = (241, 0, 0)

    SHOW = (254, 0, 0)


def zigzag(val: int) -> int:
    if val >= 0:
        return val << 1
    else:
        return (-val - 1) << 1 | 1


def unzigzag(val: int) -> int:
    if val % 2 == 0:
        return val >> 1
    else:
        return (-val - 1) >> 1


@dataclass(frozen=True, slots=True)
class Instruction:
    opcode: OpCode
    arg: int | sentinel = 0
    arg2: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.arg, int | sentinel):
            raise TypeError("Instruction argument must be int or sentinel")

    def __str__(self) -> str:
        result = self.opcode.name

        if self.opcode.args >= 1 and self.opcode is not OpCode.CALL_INDIRECT:
            result += f" {self.arg}"

        if self.opcode.args >= 2:
            result += f" {self.arg2}"

        assert not isinstance(self.arg, sentinel)
        if self.opcode is OpCode.CHR:
            result += f" ({'' if self.arg == -1 else chr(self.arg)!r})"
        elif self.opcode is OpCode.BOOL:
            result += f" ({bool(self.arg)})"
        elif self.opcode is OpCode.IS_TYPE:
            result += f" ({'None' if self.arg == 0 else TYPES[self.arg].__name__})"
        elif self.opcode is OpCode.OPEN:
            result += f" ({FILE_MODES[self.arg]})"

        return result

    def __bytes__(self) -> bytes:
        if isinstance(self.arg, sentinel):
            raise TypeError("Instructions with unresolved forward references cannot be encoded")

        opcode = self.opcode.value
        if self.has_second_arg():
            if self.arg2 > 15:
                raise TypeError("Function calls with more than 15 arguments cannot be encoded")

            arg = zigzag(self.arg << 4 | self.arg2)
        else:
            arg = zigzag(self.arg)

        chunks = []
        while arg > 255:
            chunks.append(arg & 255)
            arg >>= 8
        chunks.append(arg)

        result = bytearray()
        for chunk in chunks[:0:-1]:
            result.extend((255, chunk))
        result.extend((opcode, chunks[0]))

        return bytes(result)

    def has_second_arg(self) -> bool:
        return self.opcode in {OpCode.CALL, OpCode.CALL_INDIRECT}

    def stack_effect(self) -> int:
        opcode_stack_effect = self.opcode._stack_effect
        if callable(opcode_stack_effect):
            args = self.opcode.args
            if args == 2:
                return opcode_stack_effect(self.arg, self.arg2)
            else:
                return opcode_stack_effect(self.arg)

        return opcode_stack_effect


if TYPE_CHECKING:

    @dataclass(frozen=True, slots=True)
    class ResolvedInstruction(Instruction):
        opcode: OpCode
        arg: int = 0
        arg2: int = 0
else:
    ResolvedInstruction = Instruction


@dataclass(frozen=True, slots=True, weakref_slot=True, eq=False)
class StackItem:
    obj: Any


class StackUnderflowError(Exception):
    pass


class InstructedError(Exception):
    pass


class PopPeek(Protocol):  # necessary due to the optional argument
    def __call__(self, stack: list[Any], index: int = -1, /) -> Any: ...


@dataclass(eq=False)
class VMFrame:
    current: int = 0
    stack: list[Any] = field(default_factory=list)
    global_vars: set[int] = field(default_factory=set)
    globals_: InitVar[MutableMapping[int, Any] | None] = None
    env: ChainMap[int, Any] = field(default_factory=lambda: ChainMap[int, Any]())
    prev: int | None = None

    def __post_init__(self, globals_: MutableMapping[int, Any] | None) -> None:
        self.env.maps = [{}, {} if globals_ is None else globals_]

    def store(self, var: int, value: Any) -> None:
        if var in self.global_vars:
            self.env.maps[1][var] = value
        else:
            self.env[var] = value


@dataclass
class VMState:
    frames: list[VMFrame] = field(default_factory=lambda: [VMFrame()])
