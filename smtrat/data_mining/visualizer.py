import matplotlib.pyplot as plt
import matplotlib.lines as mlines

lines = [[float(comp) for comp in (line.rstrip('\n')).replace('==',';').split(';')] for line in open('results.res')]


curOpt = 1000
for l in lines: 
    if curOpt > l[8]:
        print "set from" + str(curOpt) + " to " +str(l[8])
        curOpt = l[8]
        opt = l        

print opt

toShow = 0

attributes = ['maxContractions','targetDiameter','maxSplitNumber','gainThreshold','alpha','weightEps','minCandidates','updateFactor']

# you may also want to remove whitespace characters like `\n` at the end of each line
#Schema: maxContractions;targetDiameter;maxSplitNumber;gainThreshold;alpha;weightEps;minCandidates;updateFactor;
plt.grid(True)
#plt.subplot(421)
plt.plot([l[toShow] for l in lines],[l[8] for l in lines])
plt.plot([opt[toShow]],[opt[8]],'ro')
blue_line = mlines.Line2D(range(1), range(1), color='white', marker='o',markerfacecolor='red',
                                  markersize=10, label='Optimal '+attributes[toShow] + ' : ' + str(opt[toShow]) )
plt.legend(handles=[blue_line])
plt.title(attributes[toShow]+' vs. Time needed in seconds' )

plt.show()
