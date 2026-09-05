# flt_for_human

Anthropic has published [formalized proof of FLT](https://github.com/anthropics/fermats-last-theorem).
Our goal is to make the proof accessible to human readers.
With the proof formalization/search already done, hopefully this task is not as token intensive.
But since we want the results to be intuitive and accessible to humans the process will likely be labor intensive.
As a labor of love I hope it is not burdensome.
Ideas/collaborations welcome.

## Grounding

So what is special about having an actual formal proof?
You can type in any question about FLT to Gemini and it will pseudo-explain to you, the keyword being pseudo.
Its explanations are often self-contradictory and full of logic leaps and holes, to be expected from a general purpose agent.
Having a proof means that the explanation based off it can be well grounded.
And general purpose agent like Gemini will hopefully learn to diffuse the knowledge more reliably with input from efforts like this one.

## Accessibility

Grounding alone doesn't make a proof accessible to human readers.
Certain style of arguments are often more understandable than other styles, at least to some of us, and our tastes will surely vary.
Alternative proofs may be needed to make key steps as accessible as possible.

## Anthropic Docs

Anthropic generates [human readable docs](https://htmlpreview.github.io/?https://github.com/anthropics/fermats-last-theorem/blob/main/html/index.html), which are enriched with annotations.
Due to Github limit on the number of files per directory, the online preview will produce mostly dead links at the level of individual theorems/definitions.
But if you clone the project and drop the top level index.html into your browser it works very well.
