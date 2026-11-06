import ast
import tkinter as tk
from importlib import resources, util
from pathlib import Path
from tkinter import filedialog, messagebox, simpledialog, ttk

from stackvm._api import StackMachine
from stackvm._util import OpCode


def get_machine_from_python(file: str, root: tk.Tk) -> StackMachine | None:
    result = messagebox.askokcancel(
        title="Warning",
        message="Python code contained within the selected file will be executed.\nContinue?",
        icon="warning",
    )

    if not result:
        return None

    spec = util.spec_from_file_location("<stackvm>", file)

    if spec is None:
        messagebox.showerror(title="Error", message="Failed to load Python file")
        return None

    module = util.module_from_spec(spec)
    loader = spec.loader

    if loader is None:
        messagebox.showerror(title="Error", message="Failed to load Python file")
        return None

    try:
        loader.exec_module(module)
    except BaseException as e:  # noqa: BLE001
        messagebox.showerror(
            title="Error",
            message="Exception raised when importing module",
            detail=f"{type(e).__name__}: {e}",
        )
        return None

    candidates = {name: machine for name, machine in vars(module).items() if isinstance(machine, StackMachine)}

    if not candidates:
        messagebox.showerror(title="Error", message="No instances of StackMachine found in module globals")
        return None

    if len(candidates) >= 2:
        options = sorted(candidates)

        dialog = tk.Toplevel(root)
        dialog.title("Input")

        dialog.resizable(False, False)

        choice = tk.StringVar(value=options[0])

        tk.Label(dialog, text="Select stack machine to execute:").pack()

        ttk.Combobox(dialog, textvariable=choice, values=options, state="readonly").pack(padx=20, pady=10)

        selection: str = ""

        def submit():
            nonlocal selection
            selection = choice.get()
            dialog.destroy()

        ttk.Button(dialog, text="Select", command=submit).pack(pady=10)

        dialog.grab_set()
        root.wait_window(dialog)

        return candidates[selection]
    else:
        return next(iter(candidates.values()))


def main():
    root = tk.Tk()

    icon = resources.files("stackvm").joinpath("resources", "icon.ico")

    with resources.as_file(icon) as path:
        root.iconbitmap(path)

    try:
        root.withdraw()

        file = filedialog.askopenfilename(
            title="Select a file...",
            filetypes=[
                ("StackVM files", "*.bin *.svm"),
                ("Python files", "*.py"),
                ("All files", "*.*"),
            ],
        )

        if not file:
            return

        path = Path(file)

        if path.suffix == ".py":
            machine = get_machine_from_python(file, root)

            if machine is None:
                return
        else:
            machine = StackMachine.from_bytes(path.read_bytes())

        if any(instr.opcode is OpCode.OPEN for instr in machine.instructions):
            result = messagebox.askyesno(
                title="Warning",
                message="This program performs file I/O. Continue?",
                icon="warning",
            )
            if not result:
                return

        arg_input = simpledialog.askstring(
            title="Input",
            prompt="Enter initial arguments, separated by commas. Use quotes to indicate characters.",
        )

        if not arg_input:
            arg_input = "()"

        try:
            args = ast.literal_eval(arg_input)
        except (ValueError, SyntaxError):
            messagebox.showerror(title="Error", message="Could not parse arguments")
            return

        if not isinstance(args, tuple):
            args = (args,)

        for arg in args:
            if not (isinstance(arg, None | int | bool) or isinstance(arg, str) and len(arg) <= 1):
                messagebox.showerror(
                    title="Error",
                    message=f"Disallowed argument {arg} (only None, int, bool, and chr are permitted)",
                )
                return

        if any(instr.opcode in {OpCode.OFTEN, OpCode.SELDOM} for instr in machine.instructions):
            seed_input = simpledialog.askstring(
                title="Input",
                prompt="Enter a seed (leave blank for random):",
            )

            if seed_input is None:
                return

            if not seed_input:
                seed = None
            else:
                try:
                    seed = int(seed_input)
                except ValueError:
                    seed = seed_input
        else:
            seed = None
    finally:
        root.destroy()

    machine.ui(*args, seed=seed)


if __name__ == "__main__":
    main()
