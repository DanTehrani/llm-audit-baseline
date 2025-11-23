import { Agent } from '@mastra/core/agent';
import { openai } from '@ai-sdk/openai';
import { GroundTruthFinding, JudgeResult, Vulnerability } from './types';
import { z } from 'zod';
import { MODEL } from './utils';

export const judgeAgent: Agent = new Agent({
  name: 'Judge',
  instructions: 'You are a vulnerability finding judge',
  model: openai(MODEL),
});

export const judge = async ({
  vulnerabilities,
  groundTruthFindings,
}: {
  vulnerabilities: Vulnerability[];
  groundTruthFindings: GroundTruthFinding[];
}): Promise<JudgeResult[]> => {
  const prompt = `
    These are predicted vulnerabilities of a function of a smart contract.
	Predicted vulnerabilities: ${vulnerabilities.map(vulnerability => `- ${vulnerability.title}: ${vulnerability.summary}`).join('\n')}

	Here are the ground truth findings:
	${groundTruthFindings.map(finding => `- ${finding.id}: ${finding.title}`).join('\n')}

	Return if the ground truth finding matches the predicted vulnerability.
	Mark ground truth finding that was identified in the predicted vulnerabilities as "matched".
	Mark ground truth finding that was not identified in the predicted vulnerabilities as "missed".

	You should return an array that has the same length as the ground truth findings.
	Each element in the array should be an object with the following properties:
		- id: The id of the ground truth finding
		- result: If the finding was identified in the provided predicted vulnerabilities

	Just return the JSON object. No other text.
  `;

  const judgeResult = await judgeAgent.generate(prompt, {
    output: z.object({
      results: z.array(
        z.object({
          id: z.string().describe('The id of the ground truth finding'),
          matched: z
            .boolean()
            .describe(
              'If the ground truth finding was identified in the provided predicted vulnerabilities'
            ),
        })
      ),
    }),
  });

  return judgeResult.object.results as JudgeResult[];
};
