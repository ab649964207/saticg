fb=open('temp','w')
# def mod1(i,j):
#     i=str(i)
#     j=str(j)
#     str1='X%'+i+'=='+j
#     print(str1)
#     fb.write(str1+'\n')
# for i in range(2,31):
#     for j in range(0,i):
#         mod1(i,j)
for i in range(0,50):
    if(i%11==1 or i%11==2 or i%11==5 or i%11==8):
        fb.write(str(i)+',')