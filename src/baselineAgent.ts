import { Agent } from '@mastra/core/agent';
// import { openai } from '@ai-sdk/openai';
import { getMinifiedCode, MODEL, toBulletPoints } from './utils';
import { z } from 'zod';
import type { Vulnerability } from './types';
import { openai } from '@ai-sdk/openai';
import fs from 'fs';
import { SourceUnit } from './SourceUnit';

export const baselineAgent: Agent = new Agent({
  name: 'Baseline Auditor',
  instructions: 'You are a smart contract vulnerability finder',
  model: openai(MODEL),
});

export const findVulnerabilities = async (
  sourceUnit: SourceUnit
): Promise<Vulnerability[]> => {
  const minimizedCode = await getMinifiedCode(sourceUnit);

  const prompt = `
  Audit the following contract for vulnerabilities:
  ${minimizedCode}

  If you cannot find any vulnerabilities, return the following JSON object:
  {{	
    "vulnerabilities": []
  }}
  `;

  const auditResult = await baselineAgent.generate(prompt, {
    output: z.object({
      vulnerabilities: z.array(
        z
          .object({
            title: z.string().describe('The title of the vulnerability'),
            summary: z
              .string()
              .describe('A short summary of the vulnerability'),
          })
          .describe('A vulnerability found in the contract')
      ),
    }),
  });

  return auditResult.object.vulnerabilities as Vulnerability[];
};
