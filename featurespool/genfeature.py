

from ast import If
from cgi import print_arguments
import numpy
import time

start = time.time()

# winSet=[1,2,4,5,6,8,9,10,12,13,15,16,17,19,20,21,23,24,26,27,28,30,31,32,34,35,37,38,39,41,42,43,45,46,48,49]
# loseSet=[0,3,7,11,14,18,22,25,29,33,36,40,44,47,49]
winSet=[[1, 1], [2, 2], [3, 3], [4, 4], [5, 5], [6, 6], [7, 7], [8, 8], [9, 9]]
loseSet=[[1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [1, 8], [1, 9], [2, 1], [2, 3], [2, 4], [2, 5], [2, 6], [2, 7], [2, 8], [2, 9], [3, 1], [3, 2], [3, 4], [3, 5], [3, 6], [3, 7], [3, 8], [3, 9], [4, 1], [4, 2], [4, 3], [4, 5], [4, 6], [4, 7], [4, 8], [4, 9], [5, 1], [5, 2], [5, 3], [5, 4], [5, 6], [5, 7], [5, 8], [5, 9], [6, 1], [6, 2], [6, 3], [6, 4], [6, 5], [6, 7], [6, 8], [6, 9], [7, 1], [7, 2], [7, 3], [7, 4], [7, 5], [7, 6], [7, 8], [7, 9], [8, 1], [8, 2], [8, 3], [8, 4], [8, 5], [8, 6], [8, 7], [8, 9], [9, 1], [9, 2], [9, 3], [9, 4], [9, 5], [9, 6], [9, 7], [9, 8]]

featurePool=[]
for line in open(r"icgsat\feature2.io"):
    line=line.replace('\n','')
    featurePool.append(line)

lenwinset=len(winSet)
lenloseset=len(loseSet)
lenfeaturesPool=len(featurePool)
# Initialize the array to store all boolean values at each position
winfeatures=numpy.zeros((lenwinset,lenfeaturesPool),dtype = int)
losefeatures=numpy.zeros((lenloseset,lenfeaturesPool),dtype = int)



def FeatureCheck(numset,targetset):
    for i in range(0,len(numset)):
        for j in range(0,lenfeaturesPool):
            X=numset[i][0]
            if(len(winSet[0])==1):
                if(eval(featurePool[j])):
                    targetset[i][j]=1
            if(len(winSet[0])==2):
                Y=numset[i][1]
                if(eval(featurePool[j])):
                    targetset[i][j]=1




FeatureCheck(winSet,winfeatures)
FeatureCheck(loseSet,losefeatures)

print(winfeatures)
print(losefeatures)

# Compare the selected features to check if they satisfy the fourth constraint
def isConstraintChenk(*v):
    i1=v[0]-1
    # print(featurePool[i1])
    if(len(v)==1):
        for i in range(0,lenwinset):
            for j in range(0,lenloseset):
                if(winfeatures[i][i1]^losefeatures[j][i1]==0):
                    return False
    if(len(v)==2):
        i2=v[1]-1
        # print(featurePool[i2])
        for i in range(0,lenwinset):
            for j in range(0,lenloseset):
                if((winfeatures[i][i1]^losefeatures[j][i1])+(winfeatures[i][i2]^losefeatures[j][i2]==0)):
                    return False
    if(len(v)==3):
        i2=v[1]-1
        i3=v[2]-1


        for i in range(0,lenwinset):
            for j in range(0,lenloseset):
                if((winfeatures[i][i1]^losefeatures[j][i1]) + (winfeatures[i][i2]^losefeatures[j][i2]) + (winfeatures[i][i3]^losefeatures[j][i3])==0):
                    return False
    return True

# Generate expressions based on selected features and state values
def generateExpression(*v):
    i1=v[0]-1
    if(len(v)==1):
        if(winfeatures[0][i1]==1):
            print('winning formula:',featurePool[i1])
        else:
            print('winning formula:','Not('+featurePool[i1]+')')
    if(len(v)==2):
        tempset=[]
        i2=v[1]-1
        for i in range(0,lenwinset):
            temp = [winfeatures[i][i1],winfeatures[i][i2]]
            if(temp not in tempset):
                tempset.append(temp)
        print('bool conditions of selected features:',tempset)
        result=''
        for i in range(0,len(tempset)):
            if(tempset[i][0]==1):
                tempstr = '( '+ featurePool[i1] +' And '
            else:
                tempstr = '( Not('+featurePool[i1] +') And '
            if(tempset[i][1]==1):
                tempstr = tempstr + featurePool[i2] +')'
            else:
                tempstr = tempstr +'Not('+ featurePool[i2] +'))'
            # print(tempstr)

            result = result+tempstr
            if i<len(tempset)-1:
                result = result+' Or '
         
        print('winning formula:',result)
        return result
    if(len(v)==3):
        tempset=[]
        i2=v[1]-1
        i3=v[2]-1
        for i in range(0,lenwinset):
            temp = [winfeatures[i][i1],winfeatures[i][i2],winfeatures[i][i3]]
            if(temp not in tempset):
                tempset.append(temp)   
        print('bool conditions of selected features:',tempset)  
        result=''
        for i in range(0,len(tempset)):
            if(tempset[i][0]==1):
                tempstr = '( '+ featurePool[i1] +' And '
            else:
                tempstr = '( Not('+featurePool[i1] +') And '
            if(tempset[i][1]==1):
                tempstr = tempstr + featurePool[i2] +' And '
            else:
                tempstr = tempstr +'Not('+ featurePool[i2] +') And '
            if(tempset[i][2]==1):
                tempstr = tempstr + featurePool[i3] +')'
            else:
                tempstr = tempstr +'Not('+ featurePool[i3] +'))'
            

            result = result+tempstr
            if i<len(tempset)-1:
                result = result+' Or '
        print('winning formula:',result)
        return result      


def mainSelect():  
    for i in range (1,lenfeaturesPool+1):
        if(isConstraintChenk(i)):
            print('slected features:',featurePool[i-1])
            generateExpression(i)
            return
    print('1done')
    for i in range (1,lenfeaturesPool+1):
        for j in range (i+1,lenfeaturesPool+1):
            if(i==j):
                continue
            if(isConstraintChenk(i,j)):
                print('slected features:',featurePool[i-1],featurePool[j-1])
                generateExpression(i,j)
                return
    print('2done')
    for i in range (1,lenfeaturesPool+1):
        for j in range (i+1,lenfeaturesPool+1):
            for k in range (j+1,lenfeaturesPool+1):
                if(i==j or i==k or j==k):
                    continue
                if(isConstraintChenk(i,j,k)):
                    print('slected features:',featurePool[i-1],featurePool[j-1],featurePool[k-1])
                    generateExpression(i,j,k)
                    return

mainSelect()

elapsed = round((time.time() - start),3)
print('time cost',elapsed)

