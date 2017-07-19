f = open('params.par','w+')
f.write("#------------------------------------------------------------------------------------------------------------------------------------\n")
f.write("#Schema: maxContractions;targetDiameter;maxSplitNumber;gainThreshold;alpha;weightEps;minCandidates;updateFactor;\n")
maxContractions = 10 #updated from 1000 to 10
targetDiameter = 0.141
maxSplitNumber = 410
gainThreshold = 0.41
lowerDelta = 0.0
upperDelta = 0.03
alpha = 0.9
weightEps = 0.5
minCandidates = 5.0
updateFactor = 1.1
#10;0.141;410;0.41;0.9;0.5;5;1.1
#number ofsamplings
n = 1000


#updates
maxContractionsUpdate = maxContractions/n
targetDiameterUpdate = targetDiameter/n 
maxSplitNumberUpdate = 10*maxSplitNumber/n
gainThresholdUpdate = gainThreshold/n
#lowerDeltaUpdate = 0.0
#upperDeltaUpdate = 0.03
alphaUpdate = alpha/n
weightEpsUpdate = weightEps/n
minCandidatesUpdate = 1
updateFactorUpdate = updateFactor/n

#this bit-vector is used to represents which updates are active
active = [0,0,0,0,0,0,0,0]



for i in range(1,n+1):
    f.write(str(str(maxContractions) + ";"+str(targetDiameter) + ";" + str(maxSplitNumber) + ";" + str(gainThreshold) + ";"+str(alpha) + ";"+str(weightEps) + ";" + str(minCandidates) + ";" + str(updateFactor)+";\n"))
    maxContractions -= maxContractionsUpdate*active[0] 
    targetDiameter += targetDiameterUpdate*active[1]
    maxSplitNumber += maxSplitNumberUpdate*active[2]
    gainThreshold -= gainThresholdUpdate*active[3]
    alpha -= alphaUpdate*active[4]
    weightEps -= weightEpsUpdate*active[5]
    minCandidates += minCandidatesUpdate*active[6] 
    updateFactor -= updateFactorUpdate*active[7]
