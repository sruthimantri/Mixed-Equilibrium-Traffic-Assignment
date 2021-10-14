#!/usr/bin/env python
# coding: utf-8

# In[1]:


import os
os.getcwd()


# In[2]:


import warnings
warnings.filterwarnings('ignore')


# In[3]:


time_FW_100={}
import csv
with open('fw-time_100.csv') as f:
    csv_reader = csv.reader(f, delimiter=',')
    #line_count=0
    for row in csv_reader:
        time_FW_100.update({(int(row[0][1:]),int(row[1][:-1])):float(row[2])})
time_FW_100


# In[4]:


len(time_FW_100)


# In[5]:


import numpy as np
import math
import time
import heapq 
from collections import defaultdict
from pyomo.environ import *
from itertools import tee
from itertools import compress
import itertools
import copy
import numpy as np
from collections import OrderedDict
from scipy import optimize
from copy import deepcopy
from itertools import islice
import networkx as nx


# In[6]:


class Node: # Defining nodes as a classs
    def __init__(self, _tmpIn): # Nodes Input file is taken as tmpIn
        self.Id = int(_tmpIn[0]) # First column is assigned as id
        #self.lat = float( _tmpIn[0]) # SEcond column is assigned as lat as a float variable
        #self.lon = float( _tmpIn[1]) # Third Column is assigned as Longitude as a float variable
        self.outLinks = [] # Created an empty list with outlinks
        self.inLinks = [] # created an empty list with inlinks
        self.labels = 0 # time, cost, mode(may be?), IVT, WT, WK, TR 
        self.preds = ("","") # one is node and other link # Created an empty tuple 
class Link: #Defining Links as a class 
    def __init__(self, _tmpIn): # Read the network file as a tmpIn
        self.tailNode = int(_tmpIn[0]) #  First column is assigned as node
        self.headNode = int(_tmpIn[1]) # Second column is assigned as tail node
        self.capacity = float(_tmpIn[2]) # veh per hour
        self.length = float(_tmpIn[3]) # Length
        self.fft = float(_tmpIn[4]) # Free flow travel time (min)
        self.beta = float(_tmpIn[6])
        self.alpha = float(_tmpIn[5])
        self.flow = float(_tmpIn[7])
        self.speedLimit = float(_tmpIn[8])
        self.toll = float(_tmpIn[9])
        self.linkType = float(_tmpIn[10])
        self.time =  float(_tmpIn[4])*(1 + float(_tmpIn[5])*math.pow((float(_tmpIn[7])/float(_tmpIn[2])), float(_tmpIn[6])))
         # derived a column naming time that can be calculated using the bpr fomula in which flow is intially "0"

class Demand: #Defining Demand as a class 
    def __init__(self, _tmpIn, perc): # Reading the Demand input file as tmpIn
        self.origin = int(_tmpIn[0]) #First column is assigned as origin  
        self.dest =  int(_tmpIn[1]) # Second column is assigned as destination
        self.trips = float(_tmpIn[2]) # Third column is assigned as demand as a float variable
        self.trips_ue =  round(perc * float(_tmpIn[2]) * 0.01)
        self.trips_so =  round((100-perc) * float(_tmpIn[2]) * 0.01)   


# In[7]:


def readNodes():
    inFile = open("nodes.txt")
    tmpIn = inFile.readline().strip().split("\t")
    for x in inFile:
        tmpIn = x.strip().split("\t")
        nodeSet[tmpIn[0]] = Node(tmpIn)
    inFile.close()
    print (len(nodeSet), "nodes")

def readNetwork():
    inFile = open("network.txt")
    tmpIn = inFile.readline().strip().split("\t")
    for x in inFile:
        tmpIn = x.strip().split("\t")
        linkId = (int(tmpIn[0]), int(tmpIn[1]))
        linkSet[linkId] = Link(tmpIn)
        if tmpIn[0] not in nodeSet:
            print ("Error: Node not present")
        else:
            nodeSet[tmpIn[0]].outLinks.append(tmpIn[1])
        if tmpIn[1] not in nodeSet:
            print ("Error: Node not present")
        else:
            nodeSet[tmpIn[1]].inLinks.append(tmpIn[0])
    inFile.close()
    print (len(linkSet), "links")


perc = 10
def readDemand():
    inFile = open("demand.txt")
    tmpIn = inFile.readline().strip().split("\t")
    for x in inFile:
        tmpIn = x.strip().split("\t")
        demandId = (int(tmpIn[0]),int(tmpIn[1]))
        tripSet[demandId] = Demand(tmpIn, perc)
        routeSet[demandId] = float(tmpIn[2])
        originZones[tmpIn[0]].add(tmpIn[1])
    inFile.close()
    print (len(originZones), "origins")
    print (len(tripSet), "OD pairs")
    print (len(routeSet.keys()), "OD pairs")
    print (len(routeSet.values()), "demand") 


# In[8]:


linkSet ={}
nodeSet ={}
zoneSet = {}
routeSet = {}

originZones = defaultdict(set)
tripSet = {}

readNodes()
readNetwork()
readDemand()


# In[9]:


def pairwise(iterable):
    "s --> (s0,s1), (s1,s2), (s2,s3),...."
    a, b = tee(iterable)
    next(b, None)
    return zip(a,b)


# In[10]:


def k_shortest_path(linkSet):
    G = nx.DiGraph()
    for od_pair in linkSet.keys():   
        time = linkSet[od_pair].time
    #print(list(linkSet.keys())[i][0],list(linkSet.keys())[i][1], weight)
        G.add_edge(od_pair[0], od_pair[1], weight= time)
    allroutes_k_shortest_paths = {}
    for s,d in list(routeSet.keys()):
        paths = list(islice(nx.shortest_simple_paths(G, s, d, weight = 'weight'), 10))#k= 10
        allroutes_k_shortest_paths.update({(s,d):paths})

    allroutes_k_shortest_paths = {key: [list(pairwise(ls)) for ls in value]
                                  for key, value in allroutes_k_shortest_paths.items()}
    
    ## flatten the list of k-shortest path for entire network 
    flatten_list = list(itertools.chain.from_iterable(allroutes_k_shortest_paths.values()))
    return flatten_list, allroutes_k_shortest_paths


# In[11]:


def delta(slink, flatten_list):
    ls = []
    for route in flatten_list:
        if slink in route:
            ls.append(True)
        else:
            ls.append(False)
    return ls


# In[12]:


def SO(routeSet, linkSet, allroutes_k_shortest_paths, flatten_list, tripSet):
    #print('-- ## SO Function ## --')
                        
    #print ('-- ## Pyomo model ## --')
    ## Create Index labels for pyomo 
    d_k_shortestpath_orig = deepcopy(allroutes_k_shortest_paths)
    
    for k,v in allroutes_k_shortest_paths.items():
        i=1
        for index, ele in enumerate(v):
            v[index] = str(k[0])+'_'+str(k[1])+'_'+str(i)
            i +=1
    flatten_list_label = list(itertools.chain.from_iterable(allroutes_k_shortest_paths.values()))
    keys_ = flatten_list_label
    values_ = flatten_list

    so_path_map = dict(zip(keys_, values_))
    
    ## Pyomo: Non-Linear Program
    model = ConcreteModel()
    
    # Set demand variables
    model.demvar = Var([val for k, v in allroutes_k_shortest_paths.items() for val in v], 
                       within=NonNegativeReals, bounds =(0,1000000))
    
    # Set flow variables
    model.flowvar = Var([(i,j) for (i,j) in linkSet], 
                        within=NonNegativeReals, bounds =(0,1000000))
    
    # Set Demand Constraint
    model.demandCons = ConstraintList()
    for (i,j) in allroutes_k_shortest_paths:
        demand_exp = 0.0
        for k in range(len(allroutes_k_shortest_paths[(i,j)])):
            #print ((i, j), k+1)
            demand_exp += model.demvar[str(i)+'_'+str(j)+'_'+str(k+1)]
        model.demandCons.add(demand_exp - tripSet[i,j].trips_so == 0.0)
    
    # Set Flow constraint
    d_k_shortestpath_slink = {}
    for route in linkSet:
        d_k_shortestpath_slink.update({route:delta(route,flatten_list)})
    
    
    model.flowCons = ConstraintList()
    for slink in linkSet:
        filtered_indices = list(compress(model.demvar, d_k_shortestpath_slink[slink]))
        flow_exp = sum(model.demvar[i] for i in filtered_indices)
        model.flowCons.add(model.flowvar[slink] - flow_exp == 0.0)
    
    ## Set Objective Function
    model.obj = Objective(expr=(sum((model.flowvar[i,j]+linkSet[i,j].flow)*((linkSet[i,j].fft + linkSet[i,j].fft * 0.15 * 
                                                     ((model.flowvar[i,j]+linkSet[i,j].flow)**4) * linkSet[i,j].capacity**-4)) 
                                for (i,j) in linkSet)),sense = minimize)
    
    
    ## Put solver ipopt or baron
    opt = SolverFactory("baron")
    
    ## solve it
    results = opt.solve(model)
    
    ## print result
    #print(model.obj.display())
    #print(model.flowvar.get_values().items())
    so_travel_times = {}
    for link, flow in model.flowvar.get_values().items():
        if flow == None:
            flow = 0
        else:
            flow = flow
        so_travel_times[link] = linkSet[link].fft + linkSet[link].fft * 0.15 *         ((flow+linkSet[link].flow)**4) * linkSet[link].capacity**-4

    #print(type(model.flowvar.get_values().items()))
    #print(model.flowvar.get_values().items())
    #print(model.flowvar.get_values())
    #print(dict(model.flowvar.get_values()))
    return so_travel_times, dict(model.flowvar.get_values().items()),         d_k_shortestpath_orig, dict(model.demvar.get_values().items()), so_path_map


# In[13]:


def updateTravelTime():
    for l in linkSet:
        linkSet[l].time = linkSet[l].fft*(1 + linkSet[l].alpha*math.pow((linkSet[l].flow/linkSet[l].capacity), 
                                                                        linkSet[l].beta))


# In[14]:


def Dijkstra(origin): # Takes origin node
    for n in nodeSet:
        nodeSet[n].label = float("inf")
        nodeSet[n].pred = ("", "")
        nodeSet[origin].label = 0
    SE = [(0, origin)]
    it = 0
    while SE:
        currentNode = heapq.heappop(SE)[1]
        currentLabel = nodeSet[currentNode].label
        it = it + 1
        for toNode in nodeSet[currentNode].outLinks:
            link = (int(currentNode), int(toNode))
            newNode = toNode
            newPred =  (currentNode, link)
            existingLabel = nodeSet[newNode].label
            newLabel = currentLabel + linkSet[link].time
            if newLabel < existingLabel:
                heapq.heappush(SE, (newLabel, newNode))
                nodeSet[newNode].label = newLabel
                nodeSet[newNode].pred = newPred
    return it


# In[15]:


def tracePreds(dest):
    prevNode, prevLink = nodeSet[dest].pred
    spLinks = [prevLink]
    while prevNode != "":
        prevNode, prevLink = nodeSet[prevNode].pred
        if prevLink != "":
            spLinks.append(prevLink)
    return spLinks


# In[16]:


def findAlpha(x_bar):
    def df(alpha):
        sum_derivative = 0 
        for l in linkSet:
            tmpFlow = (linkSet[l].flow + alpha*(x_bar[l] - linkSet[l].flow))
            tmpCost = linkSet[l].fft*(1 + linkSet[l].alpha*math.pow((tmpFlow*1.0/float(linkSet[l].capacity)), linkSet[l].beta))
            sum_derivative = sum_derivative + (x_bar[l] - linkSet[l].flow)*tmpCost        
        return sum_derivative
    def gs(x1,x2,e):
        i = 0;
        while (x2-x1)>e:
            x_r1 = x2 - 0.618*(x2 - x1)
            x_r2 = x1 + 0.618*(x2 - x1)
            if df(x_r1) <= df(x_r2):
                x2 = x_r2
                x_r2 = x_r1
                x_r1 = x2 - 0.618*(x2 - x1)
            else:
                x1 = x_r1
                x_r1 = x_r2
                x_r2  = x1 + 0.618*(x2 - x1)
            i = i + 1
        return (x_r1 + x_r2)/2.0
    alpha = gs(0,1,0.1)
    return alpha


# In[2]:


def shortest_path_travel_time_of_SO_demand(so_demand_vars, so_path_map, so_travel_times):
    '''
    Arguments: so_demand_vars = output[4], so_path_map = output[5], so_travel_times = output[6]
    Returns: Sum of average TSTT time of SO flow(from pyomo)
    '''
    dict1 = so_demand_vars ## so_demand_vars
    so_path_map = so_path_map ## so_path_map k: 528* 30 path (label for e.g, 1_3_14 v: route list [(1,2), (1,3)])
    so_filtered_pos =  {}
    for k,v in dict1.items():
        if v >= 1: # get values if demand output >= 1
            #print(k,v)
            so_filtered_pos.update({k: so_path_map[k]})
    #print(so_filtered_pos)
    
    so_travel_times = so_travel_times ## SO travel times using BPR function flow is flow (pyomo SO)+linkset[l].flow(UE)
    
    so_path_times_filtered = {}
    for k, v in so_filtered_pos.items():
        time = 0
        for i in v:
            time += so_travel_times[i]
        so_path_times_filtered.update({k:time})
    
    from collections import defaultdict
    ls = []
    for str_item in so_path_times_filtered:
        items = str_item.split("_")
        od_pair = (int(items[0]),int(items[1]))
        ls.append((od_pair, so_path_times_filtered[str_item]))
    so_path_times_unique = defaultdict(list)

    for od_pair, time in ls:
        so_path_times_unique[od_pair].append(time)
    
    
    avgTimeSODict = {}
    for k,v in dict(so_path_times_unique).items():
        # v is the list of times for od_pair k
        avgTimeSODict.update({k:(sum(v)/ len(v))})
    #print(avgTimeSODict)
    
    return sum(avgTimeSODict.values()), avgTimeSODict


# In[3]:


def assignment(type, algorithm, accuracy):
    it = 1
    gap = float("inf")
    x_bar = {}
    for l in linkSet:
        x_bar[l] = 0.0
    while gap > accuracy:
        if algorithm == "MSA" or it < 2:
            alpha = (1.0/it)
        if algorithm == "FW":
            alpha = findAlpha(x_bar)
            #print(alpha)
        for l in linkSet:
            linkSet[l].flow = alpha*x_bar[l] + (1-alpha)*linkSet[l].flow
        updateTravelTime()
        #print(list(linkSet[l].flow for l in linkSet))
        flatten_list, d_k_shortestpath = k_shortest_path(linkSet)
        #print(f"flatten list length: {len(flatten_list)}")
        #print(len(d_k_shortestpath))
        #print(f"shortes path length: {len(d_k_shortestpath)}")
        so_travel_times, so_flow, so_d_k_shortestpath_orig, so_demand_vars, so_path_map = SO(routeSet, linkSet, d_k_shortestpath, flatten_list, tripSet)
        #print(so_flow.items())
        #print(f"update so_travel_times: {so_travel_times.items()}")
        for l in linkSet:
            linkSet[l].time = so_travel_times[l] 
            #print(linkSet[l].time)
        for l in linkSet:
            x_bar[l] = 0.0
        SPTT = 0.0
        fw_shortest_path = {}
        for r in originZones:
            Dijkstra(r)
            destinations = originZones[r]
            for s in destinations:
                #shortest_path[int(r),int(s)] = list(tracePreds(s).reverse())
                #path_ls = tracePreds(s)
                #path_ls = path_ls.reverse()
                fw_shortest_path.update({(int(r),int(s)):tracePreds(s)[::-1]})
                #print(f"shortest_path between {(int(r),int(s))} is {tracePreds(s)}")
                dem = tripSet[int(r), int(s)].trips_ue
                SPTT = SPTT + nodeSet[s].label*dem
                if r != s:
                    for spLink in tracePreds(s):
                        x_bar[spLink] = x_bar[spLink] + dem
        #print([so_flow[a] for a in linkSet])
        #print(f"shorted path for all OD pairs = {shortest_path}")
        SPTT_SO, avgTimeSODict = shortest_path_travel_time_of_SO_demand(so_demand_vars, so_path_map, so_travel_times)

        TSTT = sum([linkSet[a].flow *linkSet[a].time for a in linkSet])
        gap = abs((TSTT /float(SPTT)) - 1)
        print (TSTT, SPTT, gap)
        
        if it == 1:
            gap = gap  + float("inf")
        it = it + 1
        
        if it > 5000:
            print ("The assignment did not converge with the desired gap")
            #out = adjustment_of_demand_of_disadvantaged_SO_vehicles_to_FW(tripSet, routeSet,time_FW_100, fw_shortest_path, avgTimeSODict)
            #if out==True:
             #   break
            #else:
            #    assignment("UE","FW", 0.1)       
    else:
        time_SO = {}
        for i in time_FW_100:
            if i not in avgTimeSODict:
                time_SO.update({i:0})
            else:
                time_SO.update({i:avgTimeSODict[i]})

        diff_SO_FW = {x: time_SO[x] - time_FW_100[x] for x in time_SO if x in time_FW_100 and time_SO[x] > 0} 
        selected_od_pairs = {x for x in diff_SO_FW if diff_SO_FW[x]>=0.0833}
        print(selected_od_pairs)
        if len(selected_od_pairs) != 0:
            for od_pair in selected_od_pairs:
                tripSet[od_pair].trips_so = 0.0
                tripSet[od_pair].trips_ue = tripSet[od_pair].trips 
            out = assignment("UE","FW", 0.001)
            return out
        else:
            print("selection criterion reached")
            return so_flow, fw_shortest_path, so_d_k_shortestpath_orig,so_demand_vars, so_path_map, so_travel_times, tripSet, avgTimeSODict            
            #return ("assignment converged in ", it, " iterations"), so_flow, fw_shortest_path, so_d_k_shortestpath_orig,so_demand_vars, so_path_map, so_travel_times, tripSet, avgTimeSODict
        
        #if it > 50000:
        #    print ("The assignment did not converge with the desired gap")
        #    break
    #return ("assignment converged in ", it, " iterations"), so_flow, fw_shortest_path, so_d_k_shortestpath_orig,
        #so_demand_vars, so_path_map, so_travel_times
    


# In[4]:


def print_UE_flows(so_flow):
    outFile = open("UE-SO-10-90", "w")
    tmpOut = "\tfromNode\ttoNode\tflow\ttravelTime"
    outFile.write(tmpOut+"\n")
    for l in linkSet:
        total_flow = linkSet[l].flow + so_flow[l]
        tmpOut = "\t"+str(linkSet[l].tailNode)+"\t"+str(linkSet[l].headNode)+"\t"+str(total_flow)+"\t"        +str(linkSet[l].time)
        outFile.write(tmpOut+"\n")
    outFile.close()

def printODtravelTimes():
    outFile = open("ft_input_drivingTime.dat", "w")
    tmpOut = "fromTAZ\ttoTAZ\ttravelTime"
    outFile.write(tmpOut + "\n")
    for z in zoneSet:
        Dijkstra(z)
        for z2 in zoneSet:
            tmpOut = str(z) + "\t" + str(z2) + "\t"  + str(nodeSet[z2].label)
            outFile.write(tmpOut + "\n")
    outFile.close()

output = assignment("UE","FW", 0.001)


# In[5]:


output[0]


# In[6]:


def TSTT(linkSet, so_flow):
    TSTT_UE = 0
    TSTT_SO = 0
    TSTT = 0
    for l in linkSet:
        TSTT_UE += linkSet[l].time * linkSet[l].flow
        TSTT_SO += linkSet[l].time * so_flow[l]
        TSTT = TSTT_UE+TSTT_SO
    print("TSTT_UE =%s, TSTT_SO =%s, TSTT = %s"%(TSTT_UE,TSTT_SO,TSTT))
TSTT(linkSet, output[0])


# In[7]:


so_od_path_times = {}
for link, value in output[2].items():
    ls_time =[]
    for path in output[2][link]:
        a = 0
        for i in path:
            a += linkSet[i].time
        ls_time.append(a)
    so_od_path_times.update({link:ls_time})


# In[35]:


so_avg_time_od = {}
for link, ls in so_od_path_times.items():
    so_avg_time_od.update({link:np.mean(ls)})


# In[36]:


fw_avg_time_od = {}
for link, paths in output[1].items():
    a = 0
    for od in paths:
        a += linkSet[od].time
    fw_avg_time_od.update({link:a})


# In[37]:


## FW Avg time between OD - 552
fw_avg_time_od


# In[38]:


dict1 = output[3]
so_path_map = output[4]
so_filtered_pos =  {}
for k,v in dict1.items():
    if v > 1:
        #print(k,v)
        so_filtered_pos.update({k: so_path_map[k]})
#print(so_filtered_pos)


# In[39]:


so_travel_times = output[5]


# In[40]:


so_path_times_filtered = {}
for k, v in so_filtered_pos.items():
    time = 0
    for i in v:
        time += so_travel_times[i]
    so_path_times_filtered.update({k:time})


# In[41]:


from collections import defaultdict
ls = []
for str_item in so_path_times_filtered:
    items = str_item.split("_")
    od_pair = (int(items[0]),int(items[1]))
    ls.append((od_pair, so_path_times_filtered[str_item]))
so_path_times_unique = defaultdict(list)

for od_pair, time in ls:
    so_path_times_unique[od_pair].append(time)


# In[42]:


so_path_times_unique


# In[43]:


avgTimeSODict = {}
for k,v in dict(so_path_times_unique).items():
    # v is the list of times for od_pair k
    avgTimeSODict.update({k:(sum(v)/float(len(v)))})
avgTimeSODict


# In[44]:


time_FW = {}
for i in routeSet:
    time_FW.update({i:fw_avg_time_od[i]})


# In[45]:


time_SO = {}
for i in time_FW:
    if i not in avgTimeSODict:
        time_SO.update({i:0})
    else:
        time_SO.update({i:avgTimeSODict[i]})
time_SO


# In[46]:


import csv
with open('fw-time_10.csv', 'w') as f:
    for key in time_FW.keys():
        f.write("%s,%s\n"%(key,time_FW[key]))
        
with open('so-time_10.csv', 'w') as f:
    for key in time_SO.keys():
        f.write("%s,%s\n"%(key,time_SO[key]))  

