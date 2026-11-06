from stackvm._api import StackMachine


def main() -> None:
    with StackMachine() as for_loop:
        with for_loop.block() as (input_loop, input_stop):
            for_loop.input().copy()
            for_loop.jump_false(input_stop)
            for_loop.jump(input_loop)
        for_loop.pop()
        for_loop.list()
        with for_loop.block() as (inner_loop, inner_stop):
            for_loop.size().const(1).eq().jump_true(inner_stop)
            for_loop.roll(-1).append()
            for_loop.jump(inner_loop)

        i = for_loop.new_var()
        for_loop.const(0).store(i)

        size = for_loop.new_var()
        for_loop.len().store(size)

        with for_loop.block() as (inner_loop, inner_stop):
            for_loop.load(i, size).eq().jump_true(inner_stop)
            for_loop.load(i).getitem().print()

            for_loop.load(i).const(1).add().store(i)
            for_loop.jump(inner_loop)

        for_loop.const(None).ret()

    with StackMachine() as fizzbuzz:
        i = fizzbuzz.new_var()
        fizzbuzz.const(0).store(i)

        fizz, buzz = fizzbuzz.new_global(), fizzbuzz.new_global()
        fizzbuzz.const(*"fizz ").add().add().add().add().store(fizz)
        fizzbuzz.const(*"buzz ").add().add().add().add().store(buzz)

        check_fizz, check_buzz = fizzbuzz.forward(), fizzbuzz.forward()

        with fizzbuzz.block() as (loop, _):
            fizzbuzz.load(i).const(1).add().copy(1, 1, 1).store(i)

            fizzbuzz.call(check_fizz, 1).swap().call(check_buzz, 1).add()

            skip = fizzbuzz.forward()
            fizzbuzz.copy().jump_false(skip)
            fizzbuzz.const(0, -1, None).slice().getitem()
            fizzbuzz.print().pop().pop()
            fizzbuzz.jump(loop)

            fizzbuzz.label(skip)
            fizzbuzz.pop().print()
            fizzbuzz.jump(loop)

        with fizzbuzz.block(start=check_fizz):
            fizzbuzz.const(3).mod()
            skip = fizzbuzz.forward()
            fizzbuzz.jump_true(skip)

            fizzbuzz.load(fizz).ret()

            fizzbuzz.label(skip)
            fizzbuzz.const("").ret()

        with fizzbuzz.block(start=check_buzz):
            fizzbuzz.const(5).mod()
            skip = fizzbuzz.forward()
            fizzbuzz.jump_true(skip)

            fizzbuzz.load(buzz).ret()

            fizzbuzz.label(skip)
            fizzbuzz.const("").ret()

    with StackMachine() as random:
        error = random.forward()

        random.size().const(1).eq().jump_false(error)
        random.copy().is_type(int).jump_false(error)
        random.copy().const(1).lt().jump_true(error)

        random_bit = random.forward()
        random_bits = random.forward()

        size = random.new_var()
        random.store(size)

        random.load(size).call(random_bits, 1)

        total = random.new_var()
        random.const(0).store(total)

        i = random.new_var()
        random.const(0).store(i)

        with random.block() as (loop, stop):
            random.load(i, size).eq().jump_true(stop)

            random.load(i).getitem()
            random.load(total).const(2).div().add().store(total)

            random.load(i).const(1).add().store(i)

            random.jump(loop)

        random.load(total).const(2).div().ret()

        with random.block(start=random_bits):
            random.list()

            loop = random.label()
            random.call(random_bit).append()

            random.len().copy(-1)

            ret = random.forward()
            random.eq().jump_true(ret)

            random.jump(loop)

            random.label(ret)
            random.ret()

        with random.block(start=random_bit):
            ret = random.forward()

            random.often().often().copy(1, 2)
            random.eq().jump_false(ret)

            random.pop().pop()
            random.jump(random_bit)

            random.label(ret)
            random.pop().ret()

        random.label(error)
        random.const(*"Bad args").add().add().add().add().add().add().add()
        random.error()


if __name__ == "__main__":
    main()
