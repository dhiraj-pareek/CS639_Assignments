from kast import kachuaAST
import sys
import random 
from z3 import *
sys.path.insert(0, "KachuaCore/interfaces/")
from interfaces.fuzzerInterface import *
sys.path.insert(0, '../KachuaCore/')

# Each input is of this type.
#class InputObject():
#    def __init__(self, data):
#        self.id = str(uuid.uuid4())
#        self.data = data
#        # Flag to check if ever picked
#        # for mutation or not.
#        self.pickedOnce = False
        
class CustomCoverageMetric(CoverageMetricBase):
    # Statements covered is used for
    # coverage information.
    def __init__(self):
        super().__init__()

    # TODO : Implement this


    def compareCoverage(self, curr_metric, total_metric):
        if not total_metric:
            return True
        new_coverage_percentage = len(set(curr_metric) - set(total_metric)) / len(set(curr_metric))
        improvement_threshold = 0.01
        return new_coverage_percentage >= improvement_threshold

    # TODO : Implement this
    def updateTotalCoverage(self, curr_metric, total_metric):
        total_metric= set(curr_metric + list(total_metric))
        return total_metric

class CustomMutator(MutatorBase):
    def __init__(self):
        pass

    # TODO : Implement this
    def mutate(self, input_data, coverageInfo, irList):
        mutation_type = random.choice(["fliping_bits", "random_multiplication","swapping_variables"])
        
        if mutation_type == "fliping_bits":
            for i in input_data.data.keys():
                input_data.data[i]=abs(input_data.data[i])
                print(input_data.data[i])
                for j in range(random.randint(1,5)):
                    print(input_data.data[i])
                    bit_position = random.randint(0,10)
                    mask = 1 << bit_position
                    input_data.data[i] = input_data.data[i] ^ mask
                do_negative=random.choice(["negative","positive"])
                if do_negative=="negative":
                    input_data.data[i]*=-1
        
        elif mutation_type == "random_multiplication":
             for i in input_data.data.keys():
                 r= random.randint(-5,5)
                 c= random.randint(-20,20)
                 input_data.data[i]=input_data.data[i]*r + c

        elif mutation_type == "swapping_variables":
             values = list(input_data.data.values())
             random.shuffle(values)
             shuffled_dict = {key: value for key, value in zip(input_data.data.keys(), values)}
             input_data.data=shuffled_dict

        return input_data



# Reuse code and imports from
# earlier submissions (if any).

# python kachua.py -t 100 --fuzz example/example1.tl -d {':x':5,':y':100,':z':20,':a':25}