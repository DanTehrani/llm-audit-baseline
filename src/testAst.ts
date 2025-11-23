import fs from 'fs';
import { SourceUnit } from './SourceUnit';
import { compileSol, CompilationOutput } from 'solc-typed-ast';

const testAst = async () => {
  const contractFilePath = '/Users/danieltehrani/dev/slither-ts/contract2.sol';
  // Compile the contract to AST
  const result = await compileSol(contractFilePath, 'auto', {}, [
    CompilationOutput.AST,
  ]);

  const sourceUnit = new SourceUnit(
    contractFilePath,
    result.data.sources[contractFilePath].ast
  );

  const helloFunction = sourceUnit
    .getFunctions()
    .find(func => func.name === 'hello');

  fs.writeFileSync(
    '/Users/danieltehrani/dev/slither-ts/helloFunction.json',
    JSON.stringify(helloFunction, null, 2)
  );

  if (!helloFunction) {
    throw new Error('hello function not found');
  }

  const allFunctionsReferenced = [];
  for (const statement of helloFunction.body?.statements ?? []) {
    if (statement.nodeType === 'VariableDeclarationStatement') {
      const variableDeclaration = statement.declarations[0];
      if (variableDeclaration?.nodeType === 'VariableDeclaration') {
        allFunctionsReferenced.push(variableDeclaration.name);
      }
    }
  }
};

testAst();
