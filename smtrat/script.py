f = open('params.par','w+')
f.write("#------------------------------------------------------------------------------------------------------------------------------------\n")
f.write("#Schema: maxContractions;targetDiameter;maxSplitNumber;gainThreshold;alpha;weightEps;minCandidates;updateFactor;\n")
maxContractions = 1000
targetDiameter = 0.1
maxSplitNumber = 100
gainThreshold = 0.5
lowerDelta = 0.0
upperDelta = 0.03
alpha = 0.9
weightEps = 0.5
minCandidates = 5
updateFactor = 1.1


for i in range(1,1000+1):
    f.write(str(str(maxContractions) + ";"+str(targetDiameter) + ";" + str(maxSplitNumber) + ";" + str(gainThreshold) + ";"+str(alpha) + ";"+str(weightEps) + ";" + str(minCandidates) + ";" + str(updateFactor)+";\n"))
    maxContractions -= 1
    targetDiameter += 0.005
    maxSplitNumber += 1
    gainThreshold -= 0.0005
    alpha -= 0.00089
    weightEps -= 0.0005
    minCandidates += 0.01*i
    minCandidates = int(minCandidates)
    updateFactor -= 0.001
