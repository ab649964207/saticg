from utlis.gameInit import *
import time
import numpy

start = time.time()
pddlFile = r"domain\2.Nim\2.1 Nim\Three-piled-nim(v3-le-1).pddl"  # 执行单个pddl
game_type = 'normal'   



game = GameClass(pddlFile,game_type)
Game=game.Game
winSet=game.winSet
loseSet=game.loseSet
print(winSet)
start=time.time()
featurePool=[]

def generateFeaturePool():
    if Game['var_num'] == 1:
        for line in open(r"featurespool\feature1.io"):
            line=line.replace('\n','')
            featurePool.append(line)
        return    
    if Game['var_num'] == 2:
        for line in open(r"featurespool\feature2.io"):
            line=line.replace('\n','')
            featurePool.append(line)
        return
    if Game['var_num'] == 3:
        for line in open(r"featurespool\feature3.io"):
            line=line.replace('\n','')
            featurePool.append(line)
        return
generateFeaturePool()
lenwinset=len(winSet)
lenloseset=len(loseSet)
lenfeaturesPool=len(featurePool)
# Initialize the array to store all boolean values at each position
winfeatures=numpy.zeros((lenwinset,lenfeaturesPool),dtype = int)
losefeatures=numpy.zeros((lenloseset,lenfeaturesPool),dtype = int)



def FeatureCheck(numset,targetset):
    for i in range(0,len(numset)):
        for j in range(0,lenfeaturesPool):
            if(Game['var_num'] == 1):
                X=numset[i]
                if(eval(featurePool[j])):
                    targetset[i][j]=1
            if(Game['var_num'] == 2):
                X=numset[i][0]
                Y=numset[i][1]
                if(eval(featurePool[j])):
                    targetset[i][j]=1
            if(Game['var_num'] == 3):
                X=numset[i][0]
                Y=numset[i][1]
                Z=numset[i][2]
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


def main():  
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

# main()

# print('winning formula generate time cost',round((time.time() - start),3))
