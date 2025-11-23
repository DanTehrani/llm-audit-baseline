import fs from 'fs';
import { ContractDefinition } from 'solc-typed-ast';
import { findAll } from 'solidity-ast/utils';

export class SourceUnit {
  public readonly filePath: string;
  public readonly ast: any;
  public readonly fileBuffer: Buffer;

  constructor(filePath: string, ast: string) {
    this.filePath = filePath;
    this.ast = ast;
    this.fileBuffer = fs.readFileSync(filePath);
  }

  getCodeAt(src: string) {
    const [offsetStr, lengthStr, _fileIndexStr] = src.split(':');

    const offset = Number(offsetStr);
    const length = Number(lengthStr);

    return this.fileBuffer.subarray(offset, offset + length).toString('utf8');
  }

  getInterfaces() {
    return Array.from(findAll('ContractDefinition', this.ast)).filter(
      contractDef => contractDef.contractKind === 'interface'
    );
  }

  getContracts() {
    return Array.from(findAll('ContractDefinition', this.ast));
  }

  getFunctions() {
    return Array.from(findAll('FunctionDefinition', this.ast));
  }

  getVariables() {
    return Array.from(findAll('VariableDeclaration', this.ast));
  }

  getEvents() {
    return Array.from(findAll('EventDefinition', this.ast));
  }

  getErrors() {
    return Array.from(findAll('ErrorDefinition', this.ast));
  }

  getStructs() {
    return Array.from(findAll('StructDefinition', this.ast));
  }

  getEnums() {
    return Array.from(findAll('EnumDefinition', this.ast));
  }

  getUsingForDirectives() {
    return Array.from(findAll('UsingForDirective', this.ast));
  }

  getImportDirectives() {
    return Array.from(findAll('ImportDirective', this.ast));
  }

  getPragmaDirectives() {
    return Array.from(findAll('PragmaDirective', this.ast));
  }
}
