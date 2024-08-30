from asyncio import constants
# from symbol import test
from z3 import *
import argparse
import json
import sys

sys.path.insert(0, '../KachuaCore/')

from sExecutionInterface import *
import z3solver as zs
from irgen import *
from interpreter import *
import ast

def example(s):
    # To add symbolic variable x to solver
    s.addSymbVar('x')
    s.addSymbVar('y')
    # To add constraint in form of string
    s.addConstraint('x==5+y')
    s.addConstraint('And(x==y,x>5)')
    # s.addConstraint('Implies(x==4,y==x+8')
    # To access solvers directly use s.s.<function of z3>()
    print("constraints added till now",s.s.assertions())
    # To assign z=x+y
    s.addAssignment('z','x+y')
    # To get any variable assigned
    print("variable assignment of z =",s.getVar('z'))

def checkEq(args,ir):

    file1 = open("../Submission/testData1.json","r+")
    testData1=json.loads(file1.read())
    file1.close()
    file2 = open("../Submission/testData2.json","r+")
    testData2 = json.loads(file2.read())
    file2.close()
    testData = convertTestData(testData1)
    testData2 = convertTestData(testData2)
    print('Test data 1 :\n',testData)
    print('Test data 2 :\n',testData2)
    # output = args.output
    # example(s)
    # TODO: write code to check equivalence
    s = zs.z3Solver()
    s2 = zs.z3Solver()
    s3 = zs.z3Solver()
    params = list(testData2['1']['params'].keys())
    constparams=[]
    for p in params:
        s.addSymbVar(p)
    cparams = testData['1']['constparams']
    for c in cparams:
        constparams.append(c[1:])
        s.addSymbVar(c[1:])
        s2.addSymbVar(c[1:])
    v =0
    for i in testData2:

        paramsk = list(testData2[i]['params'].keys())
        paramsv = list(testData2[i]['params'].values())
        cparams = testData['1']['constparams']
        c = 0
        for t in paramsk:
            s.addAssignment(t,str(paramsv[c]))
            s2.addAssignment(t,str(paramsv[c]))
            c += 1
        km = []
        for h in testData: 
            l = len(testData[h]['constraints'])
            while(l > 0):
                s.addConstraint(testData[h]['constraints'][l-1])
                l = l-1
            if(str(s.s.check()) == 'sat'):
                km.append(h) 
            s.s.reset()
        
        if(len(km)==1):
            for key, value in testData2.items():
                symbEnc1 = testData[key]['symbEnc']
                params_str = value["params"]
                for k, val in testData.items():
                    symbEnc2 = testData2[k]['symbEnc']
                    constraints = val["constraints"]
                    temp="And("
                    for key2,value2 in params_str.items():
                        temp = temp+key2+"=="+str(value2)+","
                    temp=temp+constraints[0]+")"
                    s.s.reset()
                    s.addConstraint(temp)
                    result = s.s.check()
                    if result == sat:
                        for keyMatch in symbEnc1:
                            for k in symbEnc2:
                                if(keyMatch == k):
                                    s2.addConstraint(symbEnc1[keyMatch] + "==" +symbEnc2[k])
        
        else:
            temp = zs.z3Solver()
            Orconstraint = ""
            for var in testData[km[0]]['symbEnc']:
                temp.addSymbVar(var)
            for k in km:
                for c in testData[k]['constraints']:
                    temp.addConstraint(c)
                for q in testData2[i]['symbEnc']:
                    for p in testData[k]['symbEnc']:
                        if(q == p):
                            temp.addConstraint(testData2[i]['symbEnc'][q] + '==' +testData[k]['symbEnc'][p])
                l = len(str(temp.s.assertions()))
                Or_iter = str(temp.s.assertions())[1:l-1]
                Or_iter = 'And(' + Or_iter + ')'
                Orconstraint = Orconstraint + Or_iter + ","
                temp.s.reset()   
            Orconstraint=Orconstraint[:-1]
            symvar = testData2[i]['params']
            for var in symvar.keys():
                s3.addAssignment(str(var),str(symvar[var]))
            s3.addConstraint("Or(" + Orconstraint + ")")

        v+= 1
    if(len(km)==1):
        print("EQUATIONS FORMED:\n",s2.s.assertions())
        print("=> Satisfibility: ",s2.s.check())
        if(str(s2.s.check()) == 'sat'):
            print("VALUES FOR CONSTANT PARAMETERS FOR SYMBOLIC EXECUTION: ",s2.s.model())
        else:
            print("MODEL IS UNSATISFIABLE")
    else:
        print("EQUATIONS FORMED:\n",s3.s.assertions())
        print("=> Satisfibility: ",s3.s.check())
        if(str(s3.s.check()) == 'sat'):
            print("VALUES FOR CONSTANT PARAMETERS FOR SYMBOLIC EXECUTION: ",s3.s.model())
        else:
            print("MODEL IS UNSATISFIABLE") 


if __name__ == '__main__':
    cmdparser = argparse.ArgumentParser(
        description='symbSubmission for assignment Program Synthesis using Symbolic Execution')
    cmdparser.add_argument('progfl')
    cmdparser.add_argument(
        '-b', '--bin', action='store_true', help='load binary IR')
    cmdparser.add_argument(
        '-e', '--output', default=list(), type=ast.literal_eval,
                               help="pass variables to kachua program in python dictionary format")
    args = cmdparser.parse_args()
    ir = loadIR(args.progfl)
    checkEq(args,ir)
    exit()