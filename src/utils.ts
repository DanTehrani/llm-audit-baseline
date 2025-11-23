import fs from 'fs';
import { SourceUnit } from './SourceUnit';
import { encoding_for_model } from 'tiktoken';
import * as readline from 'readline';

export const MODEL = 'gpt-5-nano';

const extractFileName = (line: string): string | null => {
  const match = line.match(/\/([^/]+\.sol)\b/);
  if (match) {
    return match[1];
  }

  return null;
};

const OZ_CONTRACTS_TO_KEEP = ['ERC4626', 'AccessControl'];

const getOzContractsNames = async (path: string) => {
  const fileStream = fs.createReadStream(path);

  const rl = readline.createInterface({
    input: fileStream,
    crlfDelay: Infinity, // handles \r\n properly
  });

  const ozContracts = new Set<string>();
  for await (const line of rl) {
    if (line.toLowerCase().includes('openzeppelin') && line.includes('.sol')) {
      const fileName = extractFileName(line);
      if (fileName) {
        const contractName = fileName.replace('.sol', '');
        if (!OZ_CONTRACTS_TO_KEEP.includes(contractName)) {
          ozContracts.add(contractName);
        }
      }
    }
  }

  return Array.from(ozContracts);
};

export const getMinifiedCode = async (sourceUnit: SourceUnit) => {
  // TODO: Don't add duplicate contracts to the code
  // Get all interfaces
  const interfaces = sourceUnit.getInterfaces();

  let minimizedCode = fs.readFileSync(sourceUnit.filePath, 'utf8');

  // Replace all interfaces with empty string
  for (const interfaceDef of interfaces) {
    const interfaceCode = sourceUnit.getCodeAt(interfaceDef.src);
    minimizedCode = minimizedCode.replaceAll(interfaceCode, '');
  }

  const ozContractsNames = await getOzContractsNames(sourceUnit.filePath);
  const ozContracts = sourceUnit
    .getContracts()
    .filter(contract => ozContractsNames.includes(contract.name));

  for (const ozContract of ozContracts) {
    const ozContractCode = sourceUnit.getCodeAt(ozContract.src);
    minimizedCode = minimizedCode.replaceAll(ozContractCode, '');
  }

  return minimizedCode;
};

export const toBulletPoints = (items: string[]) => {
  return items.map(item => `- ${item}`).join('\n');
};

export const getTokenCount = (code: string) => {
  const encoding = encoding_for_model('gpt-4o');
  return encoding.encode(code).length;
};
