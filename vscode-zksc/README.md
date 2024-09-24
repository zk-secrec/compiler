
# Building

## Building zksc-language-server

Compile zksc-language-server in the top-level directory of the ZK-SecreC
compiler source tree. You can read the README.md there.

After compiling you should make sure that zksc-language-server is located
somewhere you know. For example, run `stack install` after compiling which
copies the binary to `$HOME/.local/bin/zksc-language-server`.

## Building the VS Code extension

Install npm and node using [nvm](https://github.com/nvm-sh/nvm).
This is necessary as the version of nodejs that Ubuntu supplies is most likely too old.

Install project dependencies (in the vscode-zksc directory):

`$ npm ci`

Compile:

```bash
$ export NODE_OPTIONS=--openssl-legacy-provider
$ npm run package
```

Note that defining NODE_OPTIONS might not be necessary but it is required
with some older OpenSSL versions.

# Installing

1. Open the extensions manager in VS Code (shortcut: Ctrl + Shift + X).

1. Open the menu with the ellipsis icon (...) on the right of the EXTENSIONS
   title.

1. Choose "Install from VSIX...".

1. Locate the *.vsix file that you built and click Install.

# Configuring

1. Press Ctrl + , to open the settings.

1. Search for "zk-secrec". You will find ZK-SecreC extension configuration
   options.

1. Change the server path to where your zksc-language-server binary is. Note
   that there is no variable expansion here.

# Running in VS Code Extension Development mode

This is useful if you are developing the extension.

1. Open the project in VS Code.

1. Compile the extension using `npm run compile`.

1. In VS Code press F5 or click Run -> Start Debugging in the menu.

1. Choose VS Code Extension Development from the menu that opened.

Remember to configure the language server path before opening ZK-SecreC files.

If you make changes to the code you will have to recompile the program or use
`npm run watch`.

You can restart VS Code Extension Development mode using Ctrl + Shift + P and
searching for "Developer: Reload Window" in the opened menu.

# Known limitations

VS Code has a workspace concept. This extension currently only works if you
have one workspace which is likely to be sufficient for ZK-SecreC
programming. The extension is untested with multiple workspaces and is likely
to have bugs in that case.