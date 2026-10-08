# Editor plugins

Two clients of one server. The server is the `adamas-lsp` binary (§7.2); it
knows no file paths and receives text by notification, so a plugin needs
exactly two things: to bind the `.adamas` extension to its file type and to
start a process that talks over stdio.

Both are witnessed by a run, not by eye: `crates/adamas-lsp/tests/editors.rs`
starts a real editor headless, opens a corpus fixture and reads the
diagnostics **from inside the editor**.

## Neovim

`editors/nvim` is a plugin directory with the usual layout (`ftdetect/`,
`plugin/`). Any plugin manager installs it; without a manager it is enough to
add it to `runtimepath`:

```vim
set runtimepath+=/path/to/adamas/editors/nvim
```

The binary is looked up on `PATH` under the name `adamas-lsp`. If it lives
elsewhere:

```lua
vim.g.adamas_lsp_cmd = { '/path/to/adamas-lsp' }
```

The run uses **0.12.4**, and it is the only checked version. The plugin uses
API that appeared by 0.8 (`vim.lsp.start`, `vim.filetype.add`,
`nvim_create_autocmd`), so it probably works there as well - but nothing was
measured below 0.12.4.

## VS Code

`editors/vscode` is an extension in plain JS, without a build step. It has one
dependency, `vscode-languageclient`, installed with `npm ci`.

```sh
cd editors/vscode && npm ci
```

Running from source is `--extensionDevelopmentPath`; packaging is
`vsce package`, installing the `.vsix` is `code --install-extension`.

The path to the server is the `adamas.server.path` setting, defaulting to
`adamas-lsp` from `PATH`.

## What is not here yet

**Highlighting.** The extension declares no `contributes.grammars`, and there
is no tree-sitter grammar for Neovim - that is track B of the same wave, and
the place for it in `package.json` is free.

**The apostrophe in auto-closing.** `'` is allowed inside a name (§4,
`put s'`), and an auto-closing pair would turn it into `s''`. So it is absent
from `language-configuration.json`, although the double quote is there.
