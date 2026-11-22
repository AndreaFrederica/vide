import type { CancellationToken } from 'vscode';
import type { LanguageClient } from 'vscode-languageclient/node';
import { CancellationTokenSource, RequestType, type Location, type TextDocumentPositionParams } from 'vscode-languageserver-protocol';

export interface TraceParams extends TextDocumentPositionParams {
  options?: { module?: string; maxDepth?: number; maxSignals?: number; maxAssignments?: number; includeCompilation?: boolean };
}

export interface TraceResult {
  schemaVersion: 1;
  revision: string;
  scope: 'file' | 'module';
  root: number;
  signals: Array<{ id: number; name: string; declaration: Location | null; signed?: boolean; packedRange?: [number, number] }>;
  assignments: Array<{
    kind: 'continuous' | 'blocking' | 'nonblocking' | 'initialization';
    location: Location;
    targets: number[];
    inputs: Array<{
      signal: number;
      kind: 'data' | 'control' | 'trigger';
      edge: 'rising' | 'falling' | 'either' | 'change' | null;
      location: Location;
    }>;
    guards: Array<{ location: Location; takenWhenTrue: boolean; expression: GuardExpression | null }>;
    caseEntries?: Array<{ selector: Location; body: Location; defaultBranch: boolean }>;
    waitEntries?: Location[];
    standaloneWaitEntries?: Location[];
    waitPredicates?: Array<{ location: Location; expression: GuardExpression }>;
    hasUnresolvedOperands: boolean;
    value?: AssignmentValue;
    targetRange?: [number, number];
    targetElementIndex?: AssignmentValue;
    elementValue?: AssignmentValue;
  }>;
  frontier: Array<{ signal: number; reason: 'depth' | 'signals' | 'assignments' }>;
  diagnostics: string[];
  compilation?: {
    roots: string[]; files: string[]; includeDirs: string[];
    topModules: string[]; parameterOverrides: string[]; defaultTimescale?: string;
    defines: string[]; complete: boolean;
  };
}

export type GuardExpression =
  | { op: 'signal'; args: number }
  | { op: 'not'; args: GuardExpression }
  | { op: 'and' | 'or'; args: [GuardExpression, GuardExpression] }
  | { op: 'value'; args: AssignmentValue };

type AssignmentValue =
  | { op: 'typeShape'; args: [number, boolean] }
  | { op: 'caseMatch'; args: [AssignmentValue, [AssignmentValue, AssignmentValue?][], [number, number], 'equal' | 'wildcardZ' | 'wildcardX' | 'inside'] }
  | { op: 'membership'; args: [AssignmentValue, [AssignmentValue, AssignmentValue?][], [number, number]] }
  | { op: 'signal'; args: number }
  | { op: 'unsignedBit' | 'fillBit'; args: boolean }
  | { op: 'fillUnknown'; args: 'x' | 'z' }
  | { op: 'literal'; args: [string, boolean] }
  | { op: 'select'; args: [number, number, number] }
  | { op: 'bitSelect'; args: [number, AssignmentValue] }
  | { op: 'concat'; args: AssignmentValue[] }
  | { op: 'unary'; args: ['bitNot' | 'not' | 'reduceAnd' | 'reduceOr' | 'reduceXor', AssignmentValue] }
  | { op: 'binary'; args: ['bitAnd' | 'bitOr' | 'bitXor' | 'and' | 'or' | 'equal' | 'notEqual' | 'caseEqual' | 'caseNotEqual' | 'caseItemEqual' | 'caseItemZ' | 'caseItemX' | 'less' | 'lessEqual' | 'greater' | 'greaterEqual' | 'add' | 'subtract', AssignmentValue, AssignmentValue] }
  | { op: 'conditional'; args: [AssignmentValue, AssignmentValue, AssignmentValue] };

export interface VideAnalysisApi {
  readonly version: 1;
  readonly capabilities: { readonly staticTraceVersion?: 1 };
  traceDrivers(params: TraceParams, token?: CancellationToken): Promise<TraceResult | null>;
  traceLoads(params: TraceParams, token?: CancellationToken): Promise<TraceResult | null>;
  openTraceProject?(manifest: string): Promise<VideTraceProject>;
  openTraceProjectFile?(manifestPath: string): Promise<VideTraceProject>;
}

export interface VideTraceProject extends Pick<VideAnalysisApi, 'traceDrivers' | 'traceLoads'> {
  readonly closed: boolean;
  dispose(): void;
}

export const traceDrivers = new RequestType<TraceParams, TraceResult | null, void>('vide/traceDrivers');
export const traceLoads = new RequestType<TraceParams, TraceResult | null, void>('vide/traceLoads');

export async function runTraceRequest<T>(
  request: (token: CancellationToken) => Promise<T>,
  parent?: CancellationToken,
  timeoutMs = 60_000,
): Promise<T> {
  if (parent?.isCancellationRequested) throw new Error('The VIDE RTL trace was cancelled.');
  const source = new CancellationTokenSource();
  let cancel: ((error: Error) => void) | undefined;
  const interrupted = new Promise<never>((_, reject) => { cancel = reject; });
  const interrupt = (message: string) => {
    cancel?.(new Error(message));
    source.cancel();
  };
  const registration = parent?.onCancellationRequested(() => interrupt('The VIDE RTL trace was cancelled.'));
  const timer = setTimeout(() => interrupt('The VIDE RTL trace timed out.'), timeoutMs);
  try {
    return await Promise.race([
      interrupted,
      Promise.resolve().then(() => {
        if (source.token.isCancellationRequested) return interrupted;
        return request(source.token);
      }),
    ]);
  } finally {
    clearTimeout(timer);
    registration?.dispose();
    source.dispose();
  }
}

export function createAnalysisApi(getClient: () => LanguageClient | undefined): VideAnalysisApi {
  function supportsTrace(client: LanguageClient | undefined): client is LanguageClient {
    return client?.isRunning() === true &&
      client.initializeResult?.capabilities.experimental?.videTrace?.schemaVersion === 1;
  }

  async function trace(
    method: RequestType<TraceParams, TraceResult | null, void>,
    params: TraceParams,
    token?: CancellationToken,
  ): Promise<TraceResult | null> {
    const client = getClient();
    if (!supportsTrace(client)) {
      throw new Error('The active VIDE language server does not support RTL trace schema 1.');
    }
    const result = await runTraceRequest((requestToken) =>
      client.sendRequest(method, params, requestToken), token);
    if (client !== getClient()) {
      throw new Error('The VIDE language server restarted during the RTL trace request.');
    }
    if (result && result.schemaVersion !== 1) {
      throw new Error('Unsupported RTL trace result schema.');
    }
    return result;
  }

  return {
    version: 1,
    get capabilities(): VideAnalysisApi['capabilities'] {
      return supportsTrace(getClient()) ? { staticTraceVersion: 1 } : {};
    },
    traceDrivers: (params, token) => trace(traceDrivers, params, token),
    traceLoads: (params, token) => trace(traceLoads, params, token),
  };
}
