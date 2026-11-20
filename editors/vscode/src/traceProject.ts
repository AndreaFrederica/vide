import { spawn } from 'node:child_process';
import { rmSync } from 'node:fs';
import { mkdtemp, rm, stat, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { basename, dirname, isAbsolute, join } from 'node:path';
import { pathToFileURL } from 'node:url';
import type * as vscode from 'vscode';
import {
  createProtocolConnection,
  InitializeRequest,
  InitializedNotification,
  LSPErrorCodes,
  ResponseError,
  type RequestType,
} from 'vscode-languageserver-protocol/node';
import { runTraceRequest, traceDrivers, traceLoads, type TraceParams, type TraceResult, type VideTraceProject } from './analysisApi';

export async function openTraceProject(
  input: { manifest: string } | { manifestPath: string },
  launch: { command: string; args: string[]; cwd: string; env: NodeJS.ProcessEnv },
  log: (line: string) => void,
): Promise<VideTraceProject> {
  const existing = 'manifestPath' in input;
  let root: string;
  if (existing) {
    if (!isAbsolute(input.manifestPath) || basename(input.manifestPath) !== 'vide.toml' || !(await stat(input.manifestPath)).isFile()) {
      throw new Error('Select an existing vide.toml project manifest.');
    }
    root = dirname(input.manifestPath);
  } else {
    root = await mkdtemp(join(tmpdir(), 'vide-trace-'));
    try {
      await writeFile(join(root, 'vide.toml'), input.manifest, { flag: 'wx' });
    } catch (error) {
      await rm(root, { recursive: true, force: true });
      throw error;
    }
  }

  const child = spawn(launch.command, launch.args, { cwd: launch.cwd, env: launch.env, windowsHide: true });
  const connection = createProtocolConnection(child.stdout, child.stdin);
  let closed = false;
  const dispose = () => {
    if (closed) return;
    closed = true;
    connection.dispose();
    child.kill();
    if (existing) return;
    try {
      rmSync(root, { recursive: true, force: true });
    } catch (error) {
      log(String(error));
    }
  };
  child.stderr.on('data', (data) => log(`[Trace project] ${String(data).trimEnd()}`));
  const ready = new Promise<void>((resolve, reject) => {
    child.once('error', reject);
    child.once('exit', (code) => reject(new Error(`VIDE trace project exited (${code}).`)));
    connection.onClose(() => reject(new Error('VIDE trace project closed its connection.')));
    connection.onNotification('vide/projectStatus', (status: { state: string; errors?: string[] }) => {
      if (status.state === 'loaded') resolve();
      else if (status.state === 'error' || status.state === 'none') {
        reject(new Error(status.errors?.join('\n') || 'VIDE could not load the trace manifest.'));
      }
    });
  });
  // Observe early startup failures while the initialize request is in flight.
  void ready.catch(() => undefined);
  child.once('error', dispose);
  child.once('exit', dispose);
  connection.onClose(dispose);
  connection.listen();

  async function initialize() {
    const uri = pathToFileURL(root).href;
    const initial = await connection.sendRequest(InitializeRequest.type, {
      processId: process.pid,
      rootUri: uri,
      workspaceFolders: [{ name: basename(root), uri }],
      capabilities: { general: { positionEncodings: ['utf-16'] } },
    });
    if (initial.capabilities.experimental?.videTrace?.orderedProjectSources !== true) {
      throw new Error('The VIDE language server needs ordered trace project support.');
    }
    await connection.sendNotification(InitializedNotification.type, {});
    await ready;
  }

  let timer: ReturnType<typeof setTimeout> | undefined;
  try {
    await Promise.race([
      initialize(),
      new Promise<never>((_, reject) => {
        timer = setTimeout(() => reject(new Error('VIDE trace project loading timed out.')), 120_000);
      }),
    ]);
  } catch (error) {
    dispose();
    throw error;
  } finally {
    clearTimeout(timer);
  }

  async function trace(
    method: RequestType<TraceParams, TraceResult | null, void>,
    params: TraceParams,
    token?: vscode.CancellationToken,
  ) {
    if (closed) throw new Error('VIDE trace project is closed.');
    return runTraceRequest(async (requestToken) => {
      while (!requestToken.isCancellationRequested) {
        try {
          return await connection.sendRequest(method, params, requestToken);
        } catch (error) {
          if (!(error instanceof ResponseError) ||
              error.code !== LSPErrorCodes.ContentModified ||
              !error.message.includes('VIDE is still indexing the trace project')) throw error;
          await new Promise((resolve) => setTimeout(resolve, 100));
        }
      }
      throw new Error('The VIDE RTL trace was cancelled.');
    }, token);
  }

  return {
    get closed() { return closed; },
    dispose,
    traceDrivers: (params, token) => trace(traceDrivers, params, token),
    traceLoads: (params, token) => trace(traceLoads, params, token),
  };
}
