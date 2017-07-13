import matplotlib.pyplot as plt

lines = [[comp for comp in (line.rstrip('\n')).replace('==',';').split(';')] for line in open('results.res')]
# you may also want to remove whitespace characters like `\n` at the end of each line
#Schema: maxContractions;targetDiameter;maxSplitNumber;gainThreshold;alpha;weightEps;minCandidates;updateFactor;
plt.grid(True)
plt.subplot(421)
plt.loglog([l[0] for l in lines],[l[8] for l in lines])
plt.title('LogLog:MaxContractions vs. Time needed in seconds')
#now targetDiameter vs. time 
plt.subplot(422)
plt.loglog([l[1] for l in lines],[l[8] for l in lines])
plt.title('LogLog:TargetDiameter vs. Time needed in seconds')
#now maxSplitNumber vs. time needed
plt.subplot(423)
plt.loglog([l[2] for l in lines],[l[8] for l in lines])
plt.title('LogLog:MaxSplitNumber vs. Time needed in seconds')
#now GainThreshold vs. time needed
plt.subplot(424)
plt.loglog([l[3] for l in lines],[l[8] for l in lines])
plt.title('LogLog:GainThreshold vs. Time needed in seconds')
#now Alpha vs. time needed
plt.subplot(425)
plt.loglog([l[4] for l in lines],[l[8] for l in lines])
plt.title('LogLog: Alpha vs. Time needed in seconds')
#now weightEps vs. time needed
plt.subplot(426)
plt.loglog([l[5] for l in lines],[l[8] for l in lines])
plt.title('LogLog: weightEps vs. Time needed in seconds')
#now minCandidates vs. time needed
plt.subplot(427)
plt.loglog([l[6] for l in lines],[l[8] for l in lines])
plt.title('LogLog: minCandidates vs. Time needed in seconds')
#now updateFactor vs. time needed
plt.subplot(428)
plt.loglog([l[7] for l in lines],[l[8] for l in lines])
plt.title('LogLog: updateFactor vs. Time needed in seconds')
plt.show()
