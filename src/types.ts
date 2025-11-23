export interface Vulnerability {
  title: string;
  summary: string;
}

export interface EvalResult {
  contractName: string;
  vulnerabilities: Vulnerability[];
  judgeResult: JudgeResult[];
}

export interface JudgeResult {
  id: string;
  matched: boolean;
}

export interface GroundTruthFinding {
  id: string;
  title: string;
  description: string;
  severity: string;
  contract_name: string;
  project_name: string;
  unique_key: string;
}
