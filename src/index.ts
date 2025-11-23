import 'dotenv/config';
import { compileSol, CompilationOutput } from 'solc-typed-ast';
import { SourceUnit } from './SourceUnit';
import fs from 'fs';
import * as baselineAgent from './baselineAgent';
import { judge } from './judge';
import groundTruthFindings from './ground_truth_findings.json';
import { EvalResult } from './types';

const auditContract = async (contractName: string) => {
  const contractFilePath = `/Users/danieltehrani/dev/slither-ts/contracts/${contractName}.sol`;

  // Compile the contract to AST
  const result = await compileSol(contractFilePath, 'auto', {}, [
    CompilationOutput.AST,
  ]);

  const sourceUnit = new SourceUnit(
    contractFilePath,
    result.data.sources[contractFilePath].ast
  );

  const startTime = Date.now();
  const auditResult = await baselineAgent.findVulnerabilities(sourceUnit);

  const endTime = Date.now();
  console.log(`Audit took ${((endTime - startTime) / 1000).toFixed(2)}s`);

  for (const vulnerability of auditResult) {
    console.log(`${vulnerability.title}`);
    console.log(`${vulnerability.summary}`);
    console.log(`--------------------------------`);
  }

  const contractGroundTruthFindings = groundTruthFindings.filter(
    finding => finding.contract_name === contractName
  );

  const judgeStartTime = Date.now();
  const judgeResult = await judge({
    vulnerabilities: auditResult,
    groundTruthFindings: contractGroundTruthFindings,
  });

  const judgeEndTime = Date.now();
  console.log(
    `Judge took ${((judgeEndTime - judgeStartTime) / 1000).toFixed(2)}s`
  );

  return {
    vulnerabilities: auditResult,
    judgeResult: judgeResult,
  };
};

const bench = async () => {
  const contractFiles = fs.readdirSync(
    '/Users/danieltehrani/dev/slither-ts/contracts'
  );

  const contracts = contractFiles
    .filter(file => file.endsWith('.sol'))
    .map(file => file.replace('.sol', ''));

  const allResults: EvalResult[] = [];
  for (const contract of contracts) {
    console.log(`Auditing contract ${contract}`);
    try {
      const { vulnerabilities, judgeResult } = await auditContract(contract);

      allResults.push({
        contractName: contract,
        vulnerabilities: vulnerabilities,
        judgeResult: judgeResult,
      });
    } catch (error) {
      console.error(`Error auditing contract ${contract}: ${error}`);
    }
  }

  fs.writeFileSync(
    '/Users/danieltehrani/dev/slither-ts/all-results.json',
    JSON.stringify(allResults, null, 2)
  );
};

bench();
