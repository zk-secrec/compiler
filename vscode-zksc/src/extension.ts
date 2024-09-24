/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

import * as child_process from 'child_process';
import {
  commands,
  workspace,
  window,
  ExtensionContext,
  OutputChannel
} from 'vscode';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from 'vscode-languageclient/node';

const serverBinary = 'zksc-language-server';

let client: LanguageClient;

export function activate(context: ExtensionContext) {
  const conf = workspace.getConfiguration('zk-secrec');
  let execPath = conf.serverPath;

  if (execPath === '') {
    execPath = serverBinary;
  }

  // Check if the language server binary exists
  const out = child_process.spawnSync('which', [execPath]);
  if (out.status !== 0) {
    window.showErrorMessage(`Could not find ZK-SecreC language server in zk-secrec.serverPath (value '${conf.serverPath}') or on the PATH`);
    return;
  }

  let args: string[] = [];
  if (conf.trace.server !== 'off') {
    args.push('--debug');
  }

  let runConf = {
    command: execPath,
    transport: TransportKind.stdio,
    args: args,
  };

  let serverOptions: ServerOptions = {
    run: runConf,
    debug: runConf,
  };

  let clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: 'file', language: 'zk-secrec' }],
    diagnosticCollectionName: 'ZK-SecreC',
    outputChannel: window.createOutputChannel('ZK-SecreC'),
    outputChannelName: 'ZK-SecreC',
  };

  client = new LanguageClient(
    'ZK-SecreC',
    'ZK-SecreC',
    serverOptions,
    clientOptions,
  );
  client.start();

  const restartCmd = commands.registerCommand(
    "zk-secrec.commands.restartServer",
    async () => {
      client.info('Stopping the server');
      await client.stop();
      client.info('Starting the server');
      client.start();
      client.info('Server started');
    },
  );
  context.subscriptions.push(restartCmd);

  const startCmd = commands.registerCommand(
    "zk-secrec.commands.startServer",
    async () => {
      client.info('Starting the server');
      client.start();
      client.info('Server started');
    },
  );
  context.subscriptions.push(startCmd);

  const stopCmd = commands.registerCommand(
    "zk-secrec.commands.stopServer",
    async () => {
      client.info('Stopping the server');
      await client.stop();
      client.info('Server stopped');
    },
  );
  context.subscriptions.push(stopCmd);
}

export function deactivate(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
