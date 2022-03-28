
from subfile.PDDLGrammarLexer import PDDLGrammarLexer
from subfile.PDDLGrammarParser import PDDLGrammarParser
from math import log
from z3 import *
from MyVisitor import Item, MyVisitor
from MyVisitor import game
from opera import *
from antlr4 import *

from copy import deepcopy as deepcopy
from itertools import product
import numpy
import time


X = Int('X')
X1 = Int('X1')
X2 = Int('X2')
Y = Int('Y')
Y1 = Int('Y1')
Y2 = Int("Y2")

k = Int('k')
l = Int('l')
(k1, k2, k3) = Ints('k1 k2 k3')

start = time.time()
"""=================game import========================="""
# pddlFile =sys.argv[1] #由文件main.py输入路径
# resultFile =sys.argv[2]
# game_type = sys.argv[3]
pddlFile = r"domain\1.Sub\1.1 Take-away\Take-away-3.pddl"  # 执行单个pddl

game_type = 'normal'

input_stream = FileStream(pddlFile)
lexer = PDDLGrammarLexer(input_stream)
token_stream = CommonTokenStream(lexer)
parser = PDDLGrammarParser(token_stream)
tree = parser.domain()
visitor = MyVisitor()
visitor.visit(tree)

Terminal_Condition = eval(str(game.tercondition).replace(
    'v1', 'X').replace('v2', 'X1').replace('v3', 'X2'))
Constarint = eval(str(game.constraint).replace(
    'v1', 'X').replace('v2', 'X1').replace('v3', 'X2'))
varList = []
for i in game.var_list:
    i = str(i).replace('v1', 'X').replace('v2', 'X1').replace('v3', 'X2')
    varList.append(eval(i))
actions = []




for i in game.action_list:
    one = {"action_name": i[0],
           "action_parameter": i[1],
           "precondition": eval(str(i[2]).replace('v1', 'X').replace('v2', 'X1').replace('v3', 'X2')),
           "transition_formula": eval(str(i[3]).replace('v1\'', 'Y').replace('v2\'', 'Y1').replace('v3\'', 'Y2').replace('v3', 'X2').replace('v1', 'X').replace('v2', 'X1'))}
    actions.append(one)

Game = {"Terminal_Condition": Terminal_Condition,
        "varList": varList,
        "actions": actions,
        "Constraint": Constarint,
        "var_num": game.objectsCount,
        "type": game_type,
        "appeal_constants": game.constantList}

print("Var List:",varList)
varListY = eval(str(varList).replace('X2','Y2').replace('X1','Y1').replace('X','Y'))
print("Var Y list",varListY)


print("appeal constant", Game['appeal_constants'])
print("================================================================")
"""=============================================================================="""




global_transition_formula = "Or("
for i in Game["actions"]:
    if i['action_parameter'] != []:
        temp = "["
        for j in i['action_parameter']:
            temp = temp+str(j)+","
        temp = temp[:-1]
        temp += "],"
        global_transition_formula = global_transition_formula + \
            "Exists("+temp+str(i["transition_formula"])+"),"
    else:
        global_transition_formula = global_transition_formula + \
            str(i["transition_formula"])+","

global_transition_formula = global_transition_formula[:-1]
global_transition_formula = global_transition_formula+")"

print("Global transition formula:\n\t", global_transition_formula)
global_transition_formula = simplify(eval(global_transition_formula))


position = []
if Game['var_num'] == 1:
    for i in range(0, 200):
        position.append('illegal')
elif Game['var_num'] == 2:
    for i in range(0, 100):
        position.append([])
        for j in range(0, 100):
            position[i].append('illegal')
elif Game['var_num'] == 3:
    for i in range(0, 100):
        position.append([])
        for i1 in range(0, 100):
            position[i].append([])
            for i2 in range(0, 100):
                position[i][i1].append("illegal")

"""
set all terminate state position  #求出范围内所有的终态位置 一般是一个，但有时不止一个
"""
TerminatePosition = []  # 保存已经求出来的解点坐标
while(True):
    s = Solver()
    s.add(Game["Terminal_Condition"])
    s.add(Game["Constraint"])
    if Game["var_num"] == 1:
        s.add(X < 200)
        for i in TerminatePosition:
            s.add(X != i[0])
        if(s.check() == sat):
            m = s.model()
            print(m[X])
            a = m[X].as_long()
            print('aaaaaaaaaaaaaaaaaaaaaaaaaaaaa:',a)
            TerminatePosition.append([a])
            if Game["type"] == "normal":
                position[a] = True  # normal
            else:
                position[a] = False  # misere
        else:
            break
    elif Game["var_num"] == 2:
        s.add(X < 100, X1 < 100)
        for i in TerminatePosition:
            s.add(Or(X != i[0], X1 != i[1]))
        if s.check() == sat:
            m = s.model()
            a = m[X].as_long()
            print('aaaaaaaaaaaaaaaaaaaaaaaaaaaaa:',a)
            b = m[X1].as_long()
            TerminatePosition.append([a, b])
            if(Game["type"] == "normal"):
                position[a][b] = True
            else:
                position[a][b] = False
        else:
            break
    elif Game["var_num"] == 3:
        s.add(X < 100, X1 < 100, X2 < 100)
        for i in TerminatePosition:
            s.add(Or(X != i[0], X1 != i[1], X2 != i[2]))
        if s.check() == sat:
            m = s.model()
            a = m[X].as_long()
            print('aaaaaaaaaaaaaaaaaaaaaaaaaaaaa:',a)
            b = m[X1].as_long()
            print(b)
            c = m[X2].as_long()
            print(c)
            TerminatePosition.append([a, b, c])
            if(Game["type"] == "normal"):
                position[a][b][c] = True
            else:
                position[a][b][c] = False
        else:
            break
print("All terminate position:\n\t", TerminatePosition)



def isLossingState(*v):
    print("Insert",v," into isLossingstate:")
    if len(v)==1:
        if v[0]>=200:
            return 'illegal'
    else:
        for i in v:  # default position < 100
            if i >= 100:
                return 'illegal'
    if len(v) == 1:
        if position[v[0]] != 'illegal':
            return position[v[0]]
        for x in range(0, v[0] + 1):
            if (position[x] != 'illegal'):
                continue
            temp = []
            while (True):
                s = Solver()
                s.add(global_transition_formula)
                s.add(Game["Constraint"])
                s.add(X == x)
                for i in temp:
                    s.add(Or(Y != i[0]))
                if (s.check() == sat):
                    m = s.model()
                    temp.append([m[Y].as_long()])
                else:
                    break
            is_losing = True
            s = Solver()
            s.add(Game["Constraint"])
            s.add(X == x)
            if (s.check() == unsat):
                continue
            for i in temp:
                if (position[i[0]] == 'illegal'):
                    position[i[0]] = isLossingState(i[0])
            for i in temp:
                is_losing = is_losing and not position[i[0]]
            if (is_losing):
                position[x] = True
            else:
                position[x] = False
        return position[v[0]]
    elif len(v) == 2:
        if position[v[0]][v[1]] != 'illegal':  # 已经访问过了的，直接访问值，没有的
            return position[v[0]][v[1]]
        for x in range(0, v[0]+1):  # 遍历所有的点去设置状态
            for y in range(0, v[1]+1):
                if(position[x][y] != 'illegal'):
                    continue
                temp = []  # 存放转移后的解 y y1即执行动作后的值
                while (True):
                    s = Solver()
                    s.add(global_transition_formula)
                    s.add(Game["Constraint"])
                    s.add(X == x, X1 == y)

                    for i in temp:
                        s.add(Or(Y != i[0], Y1 != i[1]))

                    if (s.check() == sat):
                        m = s.model()
                        temp.append([m[Y].as_long(), m[Y1].as_long()])  # 全局转移解
                    else:
                        break
                # print('Transilate 773 of',x,y,":\t",temp) #存放状态 438 [[2, 1], [2, 0], [1, 1]]
                is_losing = True
                s = Solver()
                s.add(Game["Constraint"])
                s.add(X == x, X1 == y)
                if(s.check() == unsat):
                    continue
                for i in temp:
                    if(position[i[0]][i[1]] == 'illegal'):
                        position[i[0]][i[1]] = isLossingState(i[0], i[1])
                for i in temp:
                    is_losing = is_losing and not position[i[0]][i[1]]
                if (is_losing):
                    position[x][y] = True
                else:
                    position[x][y] = False
        # print("判断出给定的表达式：",v,"is",position[v[0]][v[1]])
        return position[v[0]][v[1]]
    elif len(v) == 3:
        if position[v[0]][v[1]][v[2]] != 'illegal':  # 已经访问过了的，直接访问值，没有的
            return position[v[0]][v[1]][v[2]]
        for x in range(0, v[0]+1):  # 遍历所有的点去设置状态
            for y in range(0, v[1]+1):
                for z in range(0, v[2]+1):
                    if(position[x][y][z] != 'illegal'):
                        continue
                    temp = []  # 存放转移后的解 y y1即执行动作后的值
                    while (True):
                        s = Solver()
                        s.add(global_transition_formula)
                        s.add(Game["Constraint"])
                        s.add(X == x, X1 == y, X2 == z)
                        for i in temp:
                            s.add(Or(Y != i[0], Y1 != i[1], Y2 != i[2]))
                        if s.check() == sat:
                            m = s.model()
                            temp.append(
                                [m[Y].as_long(), m[Y1].as_long(), m[Y2].as_long()])  # 全局转移解
                        else:
                            break
                   
                    is_losing = True
                    s = Solver()
                    s.add(Game["Constraint"])
                    s.add(X == x, X1 == y, X2 == z)
                    if(s.check() == unsat):
                        continue
                    for i in temp:
                        if(position[i[0]][i[1]][i[2]] == 'illegal'):
                            position[i[0]][i[1]][i[2]] = isLossingState(
                                i[0], i[1], i[2])
                    for i in temp:
                        is_losing = is_losing and not position[i[0]
                                                               ][i[1]][i[2]]
                    if (is_losing):
                        position[x][y][z] = True
                    else:
                        position[x][y][z] = False
        return position[v[0]][v[1]][v[2]]

print(position)

winSet=[]
loseSet=[]
def generateWinSetandLoseSet():
    if Game['var_num'] == 1:
        for i in range(0,50):
            if ([i] in TerminatePosition):
                    loseSet.append(i)
                    continue
            if (isLossingState(i)):
                loseSet.append(i)
            else:
                winSet.append(i)
    if Game['var_num'] == 2:
        print('teminate',TerminatePosition)
        for i in range(0,10):
            for j in range(0,10):
                if ([i,j] in TerminatePosition):
                    loseSet.append([i,j])
                    continue
                if (isLossingState(i,j)):
                    loseSet.append([i,j])
                else:
                    winSet.append([i,j])


generateWinSetandLoseSet()
print(winSet)
print(loseSet)
print('winSet and loseSet generate time cost',round((time.time() - start),3))
start=time.time()
featurePool=[]

def generateFeaturePool():
    if Game['var_num'] == 1:
        for line in open(r"icgsat\feature1.io"):
            line=line.replace('\n','')
            featurePool.append(line)
        return    
    if Game['var_num'] == 2:
        for line in open(r"icgsat\feature2.io"):
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

main()

print('winning formula generate time cost',round((time.time() - start),3))
