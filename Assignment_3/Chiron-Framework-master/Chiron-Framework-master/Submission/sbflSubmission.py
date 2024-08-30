#!/usr/bin/env python3

import argparse
import math
import sys
import numpy as np

sys.path.insert(0, "../ChironCore/")
from irhandler import *
from ChironAST.builder import astGenPass
import csv


def fitnessScore(IndividualObject):
    """
    Parameters
    ----------
    IndividualObject : Individual (definition of this class is in ChironCore/sbfl.py)
        This is a object of class Individual. The Object has 3 elements
        1. IndividualObject.individual : activity matrix.
                                    type : list, row implies a test
                                    and element of rows are components.
        2. IndividualObject.fitness : fitness of activity matix.
                                    type : float
        3. Indivisual.fitness_valid : a flag used by Genetic Algorithm.
                                    type : boolean
    Returns
    -------
    fitness_score : flaot
        returns the fitness-score of the activity matrix.
        Note : No need to set/change fitness and fitness_valid attributes.
    """
    # Design the fitness function
    fitness_score = 0
    activity_mat = np.array(IndividualObject.individual, dtype="int")
    activity_mat = activity_mat[:, : activity_mat.shape[1] - 1]
    # Use 'activity_mat' to compute fitness of it.
    # ToDo : Write your code here to compute fitness of test-suite
    
    unique_columns, counts = np.unique(activity_mat, axis=1, return_counts=True)

    # Count the number of unique columns
    num_unique_columns = len(unique_columns[0])
    
    totalSum=np.sum(activity_mat)
    density=totalSum/(activity_mat.shape[0]*activity_mat.shape[1])
    
    # Use numpy.unique to get unique rows and their counts
    unique_rows, counts = np.unique(activity_mat, axis=0, return_counts=True)

    # Create a list of lists to store unique rows and their counts
    unique_rows_with_counts = []
    for row, count in zip(unique_rows, counts):
        unique_rows_with_counts.append([row.tolist(), count])

    c=0
    for i in unique_rows_with_counts:
        c+=i[1]*(i[1]-1)
    c=c/(activity_mat.shape[0]*(activity_mat.shape[0]-1))
    div=1-c
    
    fitness_score=div*(1-abs(1-2*density))*num_unique_columns

    return -1*fitness_score


# This class takes a spectrum and generates ranks of each components.
# finish implementation of this class.
class SpectrumBugs:
    def __init__(self, spectrum):
        self.spectrum = np.array(spectrum, dtype="int")
        self.comps = self.spectrum.shape[1] - 1
        self.tests = self.spectrum.shape[0]
        self.activity_mat = self.spectrum[:, : self.comps]
        self.errorVec = self.spectrum[:, -1]

    def getActivity(self, comp_index):
        """
        get activity of component 'comp_index'
        Parameters
        ----------
        comp_index : int
        """
        return self.activity_mat[:, comp_index]

    def suspiciousness(self, comp_index):
        """
        Parameters
        ----------
        comp_index : int
            component number/index of which you want to compute how suspicious
            the component is. assumption: if a program has 3 components then
            they are denoted as c0,c1,c2 i.e 0,1,2
        Returns
        -------
        sus_score : float
            suspiciousness value/score of component 'comp_index'
        """
        sus_score = 0

        # ToDo : implement the suspiciousness score function.
        cf,cp,nf,np=0,0,0,0
        for i in range(len(self.activity_mat)):
            if self.activity_mat[i][comp_index]==1:
                if self.errorVec[i]==1:
                    cf+=1
                else:
                    cp+=1
            else:   
                if self.errorVec[i]==1:
                    nf+=1
                else:
                    np+=1
        deno=math.sqrt((cf+nf)*(cf+cp))
        if deno==0:
            return 0
        return cf/deno

    def getRankList(self):
        """
        find ranks of each components according to their suspeciousness score.

        Returns
        -------
        rankList : list
            ranList will contain data in this format:
                suppose c1,c2,c3,c4 are components and their ranks are
                1,2,3,4 then rankList will be :
                    [[c1,1],
                     [c2,2],
                     [c3,3],
                     [c4,4]]
        """
        rankList = []
        # ToDo : implement rankList
        for i in range(len(self.activity_mat[0])):
            num=i+1
            first="c"+str(num)
            rankList.append([first,self.suspiciousness(i)])
        rankList = sorted(rankList, key=lambda x: x[1])
        rankList.reverse()
        rank=0
        code=-1
        for i in range(len(rankList)):
            if (rankList[i][1]!=code):
                rank+=1
                code=rankList[i][1]
            rankList[i][1]=rank
            
        print(rankList)
        return rankList


# do not modify this function.
def computeRanks(spectrum, outfilename):
    """
    Parameters
    ----------
    spectrum : list
        spectrum
    outfilename : str
        components and their ranks.
    """
    S = SpectrumBugs(spectrum)
    rankList = S.getRankList()
    with open(outfilename, "w") as file:
        writer = csv.writer(file)
        writer.writerows(rankList)
