import assert from 'node:assert/strict';
import { test } from 'node:test';
import type { LanguageClient } from 'vscode-languageclient/node';
import { CancellationTokenSource } from 'vscode-languageserver-protocol';
import { createAnalysisApi, runTraceRequest, type TraceResult } from '../src/analysisApi';

test('trace requests time out and cancel even when the server has no reply', async () => {
  let timedOut = false;
  const never = () => new Promise<never>(() => {});
  await assert.rejects(runTraceRequest((token) => {
    token.onCancellationRequested(() => { timedOut = true; });
    return never();
  }, undefined, 5), /timed out/);
  assert.equal(timedOut, true);

  const cancellation = new CancellationTokenSource();
  let forwarded = false;
  const pending = runTraceRequest((token) => {
    token.onCancellationRequested(() => { forwarded = true; });
    return never();
  }, cancellation.token);
  await Promise.resolve();
  cancellation.cancel();
  await assert.rejects(pending, /was cancelled/);
  assert.equal(forwarded, true);
  cancellation.dispose();
});

test('trace API rejects an outdated server and a reply from a restarted client', async () => {
  const params = { textDocument: { uri: 'file:///arbiter.sv' }, position: { line: 0, character: 0 } };
  let reply: (result: TraceResult | null) => void = () => {};
  const client = (schemaVersion: number, sendRequest: () => Promise<TraceResult | null>) => ({
    isRunning: () => true,
    initializeResult: { capabilities: { experimental: { videTrace: { schemaVersion } } } },
    sendRequest,
  }) as unknown as LanguageClient;
  let active = client(2, async () => null);
  const api = createAnalysisApi(() => active);
  assert.deepEqual(api.capabilities, {});
  await assert.rejects(api.traceDrivers(params), /does not support RTL trace schema 1/);

  active = client(1, () => new Promise((resolve) => { reply = resolve; }));
  assert.equal(api.capabilities.staticTraceVersion, 1);
  const old = api.traceDrivers(params);
  await Promise.resolve();
  active = client(1, async () => null);
  reply(null);
  await assert.rejects(old, /server restarted/);
  assert.equal(await api.traceLoads(params), null);
});
