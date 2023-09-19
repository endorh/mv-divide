## Multivariate Division Algorithm in Lean 4
This repository contains code from my Master's Thesis:
*Multivariate Division Algorithm in Lean 4*.

Using Lean 4 and Mathlib, we implement the multivariate division
algorithm for multivariate polynomials (`MvPolynomial`), along with
a proof of its correctness.
The termination of our algorithm is also proven by the kernel.
Our implementation is non-computable, as it depends on non-computable
definitions from Mathlib.

### Setup instructions
Lean is a complex language intended to be read and written with the aid
of an editor with LSP support.

The most complete guide of how to install both an editor (VSCode) and Lean in
all main desktop platforms can be found at the
[Lean Community website](https://leanprover-community.github.io/get_started.html).

For convenience we include excerpts of this guide below:
- [How to install Lean (using Visual Studio Code)](#how-to-install-lean-using-visual-studio-code)
  - [How to open this repository in Visual Studio Code](#how-to-open-this-repository-in-visual-studio-code)
- [How to use Lean to verify that the project compiles (without VSCode)](#how-to-use-lean-to-verify-that-the-project-compiles-without-vscode)
- [What to expect after building](#what-to-expect-after-building)

#### How to install Lean (using Visual Studio Code)
- [Install `Visual Studio Code`](https://code.visualstudio.com/download)
- Install `git`, if necessary
  - In Linux it should already be installed (otherwise use `sudo apt-get install git`)
  - In Windows, use [`git` for windows](https://gitforwindows.org)
- Install the `lean4` extension in `VSCode`
  - Open `VSCode`
  - In the leftmost vertical bar, click the *Extensions* icon
    ![Extensions icon](https://leanprover-community.github.io//img/new-extensions-icon.png)
  - In the search box that appears, type `lean4`, select the `lean4` extension that appears
    and click the install button.
- Install the Lean package manager, `elan`, using `VSCode`
  - Create a new lean file (with `.lean` extension)
  - A dialog will appear in the bottom right of your screen, saying
    `Failed to start 'lean' language server` with a button `Install Lean using Elan`
  - Click this button, and inside a terminal window within `VSCode` you should see
    the installation process begin
  - When finished, you can type `#eval 1 + 1` in the file, to verify that a blue
    underline appears under `#eval`

> Note:
  If you're on Windows, at this point you may need to restart `VSCode` from the start menu in
  order to be able to use the `lake` command from the `VSCode` terminal.

#### How to open this repository in Visual Studio Code
- Get a local copy of the repository
  - If you know how to use `git`, simply
    [clone the repository](https://docs.github.com/en/repositories/creating-and-managing-repositories/cloning-a-repository)
  - Otherwise, you may
    [download a zip archive](https://docs.github.com/en/repositories/working-with-files/using-files/downloading-source-code-archives#downloading-source-code-archives-from-the-repository-view)
    with the code.
    Extract this archive in an empty folder
- (Optional) See note below before opening Visual Studio Code
- Open Visual Studio Code
- From the `File` menu select `Open folder` (`Open` on Mac) and choose the folder that contains
  the `lakefile.lean` (must be *exactly* that folder)
- [Open a terminal in VSCode](https://code.visualstudio.com/docs/terminal/basics),
  and run the `lake update` command to download the project's dependencies
- You may now open any Lean file under the `MvDivide` folder in VSCode and a `Lean Infoview`
  should appear in the right half of your screen.
  After a long while (hopefully short if you followed the optional step), Lean will finish
  importing the Mathlib dependencies, and the yellow line in the margin should start to go down,
  as Lean processes the file.
  At this point, the `Lean Infoview` should be able to provide context information wherever you
  place your cursor
- To verify that everything compiles, you may run `lake build` from the terminal, which should
  finish without errors.

> **Note**:
  You may try to download precompiled binaries for Mathlib, though this step is likely to fail.
  Before opening VSCode (important) open a command prompt at the folder that contains the
  `lakefile.lean` file, and run
  (1) `lake update` (to download the dependencies, including Mathlib, which provides `cache`)
  and then (2) `lake exe cache get` (to download prebuilt binaries)
  Not doing this will require to build parts of Mathlib locally, which may take around 2h.
  If you do this you won't need to run `lake update` in later steps.

> Project dependencies will be stored under the `lake-packages` folder.

#### How to use Lean to verify that the project compiles (without VSCode)
- [Install `elan` manually](https://leanprover-community.github.io/install/windows.html#installing-elan-yourself)
  if you didn't install it through `VSCode`.
- [Clone](https://docs.github.com/en/repositories/creating-and-managing-repositories/cloning-a-repository)
  or
  [download](https://docs.github.com/en/repositories/working-with-files/using-files/downloading-source-code-archives#downloading-source-code-archives-from-the-repository-view)
  this repository.
- Open a command prompt at the folder containing the `lakefile.lean` file.
- Run the `lake update` command (to download project dependencies).
- (Optional) Run `lake exe cache get` to download prebuilt Mathlib binaries.
- Run the `lake build` command, which should finish without errors.

> Project dependencies will be stored under the `lake-packages` folder.

#### What to expect after building
- The `lake build` command should start building multiple files.
- After it has built `MvDivide`, it will show two messages saying:
  - *"Type of the `mv_divide_alg` algorithm:"* followed by a Lean type
  - *"Type of the `exists_mv_quorem` theorem:"* followed by a Lean type

> This will only happen once. After Lean has built the file it won't rebuild it again.
  You may rebuild it again by modifying the `MvDivide.lean` file, running `lake build` again.