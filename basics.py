#import the required libraries

from pathlib import Path
import requests
import networkx as nx #main network analysis library
import nxviz as nv
from nxviz import CircosPlot
from nxviz import ArcPlot
import matplotlib.pyplot as plt
from datetime import datetime, date
from pprint import pprint as pp
from itertools import combinations
import random
from collections import Counter, defaultdict
from matplotlib import patches
import itertools


#functions

def create_dir_save_file(dir_path: Path, url: str): #to grab files off the internet
    """
    Check if the path exists and create it if it does not.
    Check if the file exists and download it if it does not.
    """
    if not dir_path.parents[0].exists():
        dir_path.parents[0].mkdir(parents=True)
        print(f'Directory Created: {dir_path.parents[0]}')
    else:
        print('Directory Exists')
        
    if not dir_path.exists():
        r = requests.get(url, allow_redirects=True)
        open(dir_path, 'wb').write(r.content)
        print(f'File Created: {dir_path.name}')
    else:
        print('File Exists')

def find_selfloop_nodes(G):

    nodes_in_selfloops = [] #initialize empty list for data

    for x,y in G.edges(): #for each set of nodes
        if x==y: #if same node
            nodes_in_selfloops.append(x) #append node
    if nodes_in_selfloops:#if anything in list
        return nodes_in_selfloops
    else:
        print("no self loops")

def nodes_with_m_nbrs(G,m): #G is graph, m is number of neighbors the node must have
    nodes_return=set()
    
    for n in G.nodes():#for each node in graph (no metadata)
        neighbors=list(G.neighbors(n)) #list of neighbors to node n
        tot_neighbors=len(neighbors) #total number of neighbors
        if tot_neighbors==m: #if there are m neighbors
            nodes_return.add(n) #add to set

    if nodes_return:
        return nodes_return
    else:
        print("no nodes with ",n,"neighbors")


def path_exists(G, node1, node2): #determines whether or not a path exists in between nodes
    checked_nodes=set() #initialze empty set for nodes
    
    #initalize nodes to visit (queue) using node1
    queue=[node1]
    
    #iterate
    for node in queue:
        neighbors=G.neighbors(node)
        
        #check if node two is in neighbors of node one
        if node2 in neighbors:
            
            return True
            break
        else:
            checked_nodes.add(node) #otherwise, keep track of what you have visited that doesnt work
            queue.extend([n for n in neighbors if n not in checked_nodes])#extend the queue to remaining unchecked neighbors
        
        if node==queue[-1]: #if you have reached the end of the queue
            return False

def find_nodes_with_highest_deg_cent(G):
    dC_G=nx.degree_centrality(G)#compute degree centrality of all nodes
    max_C=max(list(dC_G.values())) #find maximum degree of centrality
    print("maximum degree of centrality", max_C)
    nodes=set() #intialize empty set to keep track of nodes
    
    #iterate over the degree centrality dictionary
    for k,v in dC_G.items():
        if v==max_C: #if the current value is the maximum degree of centrality
            print("value",v,"=maximum ",max_C)
            nodes.add(k) # add the node to the set
    
    return nodes
  
  
def is_in_triangle(G,n,s=2):#checks whether a given node (n) in graph (G) a triangle relationship or not.
#s is the size of the combination. This is intialized to 2, the simplist for triangle

    in_tri=False #initialize to false

    #iterate over all possible triangle relationships
    for node_1,node_2 in combinations(G.neighbors(n),s):
        #determine if the nodes share an edge
        if G.has_edge(node_1,node_2):
            in_tri=True #set condition to true
            break #discontinue search
    
    return in_tri #return boolean result

def nodes_in_triangle (G, n,s=2): #inputs=graph, node;  identifies all nodes in a triangle relationship with a given node
    tri_nodes=set([n]) #intialize tri_nodes to a set consisting of just the node
    
    for node_1, node_2 in combinations(G.neighbors(n), s): #iterating over all possible triangle combinations
        if G.has_edge(node_1,node_2): #if the two nodes share an edge
        
            tri_nodes.add(node_1) #add the nodes to the set
            tri_nodes.add(node_2)
        
    return tri_nodes


def node_in_open_triangle(G,n,s=2): #identifies whether a node is present in an open triangle with its neighbor; takes graph and node
    open_tri=False
    
    # Iterate over all possible triangle relationship combinations
    for node_1,node_2 in combinations(G.neighbors(n), s):
    
        # Check if do NOT have an edge between them
        if not G.has_edge(node_1, node_2):
            open_tri=True
            break
            
    return open_tri

def maximal_cliques (G,s) : #Takes graph and size
    maxCl=[]
    
    for cl in nx.find_cliques(G): #for each list of maximal clique nodes
        if len(cl)==s: #if of desired size
            maxCl.append(cl) #append to output list
            
    if maxCl: #if list is not empty
        return maxCl
    else:
        print("no maximal cliques of that size")

def to_uni_graph(G): #saves metadata while converting other graph types to uni-graph
    
    nodes=G.nodes(data=True)
    edges=G.edges(data=True)

    G_uni = nx.Graph()
    G_uni.add_nodes_from(nodes)
    G_uni.add_edges_from(edges)
    
    nx.set_node_attributes(G_uni, nodes) #error to resolve: AttributeError: 'NodeDataView' object has no attribute 'items'
    return G_uni

def get_nodes_and_nbrs(G, nodes_of_interest): #inputs are a graph and a list of nodes
    nodes_to_draw=[] #the structure should be a list with node1, node1 neighbors, node2, node2 neighbor
    
    for node in nodes_of_interest:
        nodes_to_draw.append(node)
        
        for nbr in (G.neighbors(node)):
            nodes_to_draw.append(nbr)

    return G.subgraph(nodes_to_draw) #return the subgraph of graph G consisting of nodes-of-interst and their neighbors
    

#body

#data and directory set up
#strings indicate where text data and images will be stored
data_dir = Path('data/2020-05-21_intro_to_network_analysis_in_python')
images_dir = Path('Images/2020-05-21_intro_to_network_analysis_in_python')

#data sources
twitter = 'https://assets.datacamp.com/production/repositories/580/datasets/64cf6963a7e8005e3771ef3b256812a5797320f0/ego-twitter.p'
github = 'https://assets.datacamp.com/production/repositories/580/datasets/69ada08d5cce7f35f38ffefe8f2291b7cfcd6000/github_users.p'

datasets = [twitter, github] #data source string to list
data_paths = list() #empty list to store modified strings

for data in datasets: #per string
    file_name = data.split('/')[-1].replace('?raw=true', '')#split spring into list delimited by the backslashes, locate file name
    data_path = data_dir / file_name #data path is data directory + filename
    create_dir_save_file(data_path, data) #create directory and save file
    data_paths.append(data_path)#append data path to empty list

#grab data off internet in network graph format

T = nx.read_gpickle(data_paths[0])
Gh = nx.read_gpickle(data_paths[1])

#explore the dataset
print(len(T)) #length of twitter graph
print(type(T.nodes())) #type of nodes
print(list(T.edges(data=True))[-1]) #access last entry...edges are dates in this case

#graph subset of data using digraph, for data with inherent directionality (example- twitter, how users interact...someone can follow someone without them followingg back)
#other graph formats are .Graph (no inherent directionality, example facebook- two friends are connected by an edge)
#and multi-edge directed graphs .MultiGraph (inherent directionality, for example 3 trips are used to model a trip between two bike stations...sometimes the multiple edges are collapsed into one summary)
#if you aren't sure what type a graph is, can check with type(graph)

T_sub = nx.DiGraph() #empty digraph format, information at https://networkx.org/documentation/networkx-1.10/reference/classes.digraph.html#networkx.DiGraph
#subset- for each entry in the first fifty entries of the dataset, if there is data, if the entry number is in this list, and less than 50, grab the data
edges_from_T = [x for x in T.edges(list(range(50)), data=True) if x[0] in [1, 16, 18, 19, 28, 36, 37, 39, 42, 43, 45] if x[1] < 50] #list will have entries as (1, 3, {'date': datetime.date(2012, 11, 16)})

T_sub.add_edges_from(edges_from_T) #add subset data to graph

#visualize data
plt.figure(figsize=(8, 8))
nx.draw(T_sub, with_labels=True)
plt.show()
plt.close()

# querying a graph using .nodes() and .edges()
#.nodes() --> list of nodes .edges() --> list of tuples with each tuple being the nodes on that edge
#for each method, argument data=True will also retreive the metadata

#example, retrieve nodes for which occupation=scientist
#entry format example, tuple (3040, {'category': 'D', 'occupation': 'scientist'})
#(node,metadata)

#two ways:
#going into the tuple
sci=[ x for x in T.nodes(data=True) if x[1]['occupation']=='scientist']
#defining d as the dictionar of data
sci = [x for x, d in T.nodes(data=True) if d['occupation'] == 'scientist']

#example, retrieve edges list of edges from before 1 Jan 2010.
#edges in format(23324, 23336, {'date': datetime.date(2010, 9, 20)}), with dates in format year, month, day
#edges are returned in format (897, 22104)
before2010=[(x,y) for x,y, d in T.edges(data=True) if d['date'].year<2010]


#creating weighted edges
#example: Set the 'weight' attribute of the edge between node 1 and 10 of T to be equal to 2.
#adding the dictionary term will create the field if it doesnt exist
T.edges[1,10]['weight']=2

#to loop through, and add weight to an edge if a particular node is involved, you can iterate
#for each entry in edges, if a particular node is involved, make its weight 2
for x,y,z in T.edges(data=True):
    if 293 in [x,y]:
        print("before",x,y,z)
        T.edges[x,y]['weight']=2
        print("after",x,y,z)

#find self-loops in graph and determine if the number of self-looping nodes in dataset is equal to that
self_loop_nodes= find_selfloop_nodes(T) #list of self-loop nodes

len(list(nx.selfloop_edges(T)))==len(self_loop_nodes)#boolean check, returns T/F

#plotting styles

#example, arcPlot(simple):
ap = nv.ArcPlot(T_sub)
plt.draw()
plt.show()
plt.close()

#matrix plots:
#does not preserve any metadata other than weight. MatrixPlot turns the graph into a matrix format, with each node having one column and one row, and edges
#manual curation
#attributes must be in dictionary format
test_attr=[ x for x in T.nodes(data=True) if x[0]<50] #make data subset for easy plotting
test_attr=dict(test_attr)

#data must be in list format, lengths and nodes must match attributes
test_data=[]
counter=0

for x,y,z in T.edges(data=True):
    if counter < len(test_attr):
        print("counter", counter)
        if x<50 and y<50:
            print(x,y,z)
            test_data.append((x,y,z))
    counter=counter+1


test_diGraph=nx.DiGraph() #create empty diGraph
test_diGraph.add_nodes_from(test_attr) #add nodes
test_diGraph.add_edges_from(test_data)#add edges
nx.set_node_attributes(test_diGraph, test_attr) #set the node attributes


m=nv.MatrixPlot(test_diGraph)#create MatrixPlot format

#taking form other graph:
m=nv.MatrixPlot(T_sub)

plt.draw()
plt.show()
plt.close()

#turning a graph into a matrix manually:
T_sub_1_0_matrix = nx.to_numpy_matrix(T_sub)
#turning a matrix into a graph manually:
T_sub_1_0_conv = nx.from_numpy_matrix(T_sub_1_0_matrix, create_using=nx.DiGraph())

# Check that the `category` metadata field is lost from each node
for n, d in T_sub_1_0_conv.nodes(data=True):
    print(n,d.keys())

#Circos Plot style (basic)- nodes are on the circumference and the edges cross the interior, more advanced plotting at https://snyk.io/advisor/python/nxviz/functions/nxviz.plots.CircosPlot

cPlot_Tsub = nv.CircosPlot(T_sub)
plt.draw()
plt.show()
plt.close()

#Arc Plot (advanced)
#advanced ArcPlots use the keyword arguments node_order and node_color, which allow the user to specify a key
#in their metadata dictionary to color and order nodes

T_subset_nodes_plt=[]
T_subset_edges_plt=[]

for count,x in enumerate(T.nodes(data=True)):
    T_subset_nodes_plt.append(x)
    T_subset_edges_plt.append(list(T.edges(data=True))[count])
    if count==49:
        break
    
T_subset_nodes_plt=dict(T_subset_nodes_plt)
    
test_diGraph=nx.DiGraph() #create empty diGraph
test_diGraph.add_nodes_from(T_subset_nodes_plt) #add nodes
test_diGraph.add_edges_from(T_subset_edges_plt)#add edges
nx.set_node_attributes(test_diGraph, T_subset_nodes_plt) #set the node attributes
     
#get rid of the weight from the earlier exercise
for x,y,z in test_diGraph.edges(data=True):
    print(type(x), type(y), type(z),z.keys())
    if 'weight' in z.keys():
        z.pop('weight')

#remove notes without attributes
nodes_to_remove=[]
for x,y in test_diGraph.nodes(data=True):
    print(x,y)
    if not y.keys():
        print("no")
        nodes_to_remove.append(x)

for node in nodes_to_remove:
    test_diGraph.remove_node(node)
    
l=dict([("celebrity","yellow"), ("politician","green"), ("scientist","purple")])

advancedArc_T= nv.ArcPlot(test_diGraph, node_color=["yellow", "green", "purple"])

# plotting- there is no functionality in NetworkX for legends so you have to create a custom one with patches
handles_dict = {patches.Patch(color=v, label=k) for k,v in l.items()}
plt.draw()
plt.legend(handles=handles_dict)
plt.show()

#ways to identify nodes that are important in a network and path-finding algorithms/degree centrality
#nodes are more important when connected to many more nodes (their neighbors)
#degree centrality (node importance)=nodes that a node are connected to/total nodes it could possibly be connected to
#if self loops, self included. If not, other nodes but self included in total possible nodes
#can use .edges() to print a list of tuples on graph
#can use list(.neighbors(n)) to return the neighbors of a node
#can use nx.degree_centrality(graph) on graph without self loops considered.

#neigbhors node one list
T_n1_neighbors=list(T.neighbors(1))
#number neighbors
len(T_n1_neighbors)


#find how many nodes in T have six neighbors
T_nodes_6=nodes_with_m_nbrs(T,6)
len(T_nodes_6)

#can compute degrees distribution across an entire graph
degree_dist_T = [len(list(T.neighbors(n))) for n in T.nodes()] #gets the degrees of every node, then gets the length of the length of degrees for each node

#The nx.degree_centrality(G) function returns a dictionary
#where the keys are the nodes and the values are their degree centrality values.

deg_central=nx.degree_centrality(T)

# Plot a histogram of the degree centrality distribution of the graph.
plt.figure()
plt.hist(list(deg_central.values()))
plt.show()

# Plot a histogram of the degree distribution of the graph
plt.figure()
plt.hist(degree_dist_T)
plt.show()

# Plot a scatter plot of the centrality distribution and the degree distribution
plt.figure()
plt.scatter(degree_dist_T, list(deg_central.values()))
plt.show()


#path finding:
##used for optimization (what is the shortest path between two points?
##modeling the spread of things (diseases, social network)
##implemented using neighbor functions
##Breadth-first search algorithm (first we determine if the destination node is in the neighbors of the first node
#if not, we move to the second degree of separation (neighbors of neighbors), and on to the nth degree


#determine which nodes in the twitter network have any neighbors
nodes_w_neighbors=[]
for n in T.nodes():#per node
    neighbors=list(T.neighbors(n)) #generaate list of neighbors
    if neighbors: #if there is anythign in the list
        print("node: ",n, " neighbors: ",neighbors)
        nodes_w_neighbors.append((n,neighbors)) #append node and neighbors as a tuple
        
nodes_w_neighbors=dict(nodes_w_neighbors) #turn into dictionary where the node is the key and the list of neighbors is the value


#manual test:
shared_neighbors=[]
for count,item in enumerate(nodes_w_neighbors.keys()): #for each node
    print("counter: ", count, "\n\nnode: ",item, "\n\n","neighbors: ",nodes_w_neighbors[item], "\n\n")
    if count<len(list(nodes_w_neighbors.keys()))-1:#account for last node
        next_node=list(nodes_w_neighbors.keys())[count+1] #next node
        print("next_node", next_node)
        if any(x in nodes_w_neighbors[item] for x in T.neighbors(next_node)):#if any of the neighbors of node 1 are in node 2
            print("shared neighbors:", item, next_node)
            shared_neighbors.append((item,next_node))#append as a tuple
        else:
            print("final node")
            
len(list(set(shared_neighbors)))#number of nodes that share neighbors


##betweeness centrality
#The number of shortest paths in a graph that pass through a node
# divided by the number of shortest paths that exist between every pair of nodes in a graph.
#This metric captures bottleneck nodes in a graph
#returns node: betweenness centrality score pairs
G = nx.barbell_graph(m1=5, m2=1) #barbell graph style- m1=nodes at ends, m2=nodes in bridge

#compute betweenness centrality of twitter network
T_bC=nx.betweenness_centrality(T)
#compute degree of centrality of twitter network
T_dC=nx.degree_centrality(T)


# Create a scatter plot of betweenness centrality and degree centrality
plt.scatter(list(T_bC.values()), list(T_dC.values()))

# Display the plot
plt.xlim(-0.00005, 0.0002)
plt.xticks(rotation=45)
plt.show()

#finding the highest degree of centrality
highest_dC_T=find_nodes_with_highest_deg_cent(T)

# Write the assertion statement to check that the identified node is correct
for node in highest_dC_T:
    assert nx.degree_centrality(T)[node] == max(nx.degree_centrality(T).values())

#identifying cliques and subgraphs
#a clique is a set of nodes that are completely connected by an edge to every other node in the set (a completely connected graph).
#to iterate over pairs of  nodes to identify cliques, rather than iterating over edges, use combinations too from the itertools library

for node_pair in list(combinations(T.node_pair(),2))[:10]: #for the first 10 pairs of nodes in graph
    (node_pair[0],node_pair[1]) #print pair

#identifying triangles (simplest complex clique)
for node in sorted(list(T.nodes())[:60]): #for the first sixty nodes in the sorted node list
    x = is_in_triangle(T, node) #define x as a Boolean value (is that node in a triangle?)
    if x == True:
        print(f'{node}: {x}')

#count the number of triangles that every node is involved in
#check if node 1 in graph T occurs in 23 triangles
try:
    assert len(nodes_in_triangle(T, 1)) == 23
except AssertionError as e: #code to run if error occurs
    print("false")
else:
    print("true")

#count the number open triangles that occur in graph T (example: A knows B, B knows c, so A may know C)
open_tri=0 #intialize counter to 0
for n in list(T.nodes()):
    if node_in_open_triangle(T,n): #if the node is in an open triangle
        open_tri +=1 #add to counter
        
print("There are "+str(open_tri)+" open triangles in the graph")

#maximal cliques (cliques that can't be extended by adding another node in the graph)
#there is a built-in function that returns the set of maximal cliques, but it does not work on digraphsgl = list(nx.find_cliques(G))
G = nx.barbell_graph(m1=5, m2=1) #generate graph
gl = list(nx.find_cliques(G)) #identify the sets of maximal cliques
print(gl) #print
nx.draw(G, with_labels=True) #compare with visualization

T_uni=to_uni_graph(T) #change T from digrpah format while preserving metadata

#subgraphs #for examination of subportions (if you are interested in the degree of centrality around a particular node, etc
#example with randomly generated graph
random.seed(121)
G = nx.erdos_renyi_graph(n=20, p=0.2)
G.nodes()
nx.draw(G, with_labels=True)
plt.show()
plt.close()

#initalize subgraph nodes as list of neighbors around node eight
G_sub_8_nodes = list(G.neighbors(8))
G_sub_8_nodes.append(8) #append the node for complete nodes required for subgraph of 8 and neighbors

G_sub_8= G.subgraph(G_sub_8_nodes) #create subgraph
G_sub_8.edges()

#visualize the subgraph
display(G_sub_8)
nx.draw(G_sub_8, with_labels=True)
plt.show()

plt.close()


#to analyze a subset of nodes in a network,copy into another graph object using G.subgraph(nodes)
#returns graph object (same type as original) comprised of the iterable of nodes passed in

nodes_of_interest = [29, 38, 42]
T_draw = get_nodes_and_nbrs(T, nodes_of_interest)
# Extract the subgraph with the nodes of interest: T_draw

#visualize
nx.draw(T_draw, with_labels=True)
plt.show()
plt.close()

#create a subgraph by subsampling by condition

# Extract the nodes of interest: nodes
#recall that T.nodes(data=True) entries have the format  23354: {'category': 'P', 'occupation': 'politician'}
#returns a list of nodes meeting the criterion that the dictionary key occupation has a value celebrity
#for the sake of brevity, will keep to first 20 items
nodes_celebs=[n for n, d in T_uni.nodes(data=True) if d["occupation"]=="celebrity" ][:20]

#turn nodes list into a set
node_set_celebs=set(nodes_celebs)

#iterate over each node in the nodes of interest list and compute their neighbors
for n in nodes_celebs:
    nbr=T_uni.neighbors(n)
    
    # Compute the union of nodeset and nbrs: nodeset
    node_set_celebs = node_set_celebs.union(nbr)


# Compute the subgraph using nodeset: T_sub
T_sub_celebs = T_uni.subgraph(node_set_celebs)
#Draw
nx.draw(T_sub_celebs, with_labels=True)
plt.show()
plt.close()

##CASE STUDIES##
#GitHub dataset (Gh) goals:
#analyze structure of the graph, including its basic properties
#visualize the graph using nxviz
#build a simple recommendation system to "connect" with one another in some fashion(users that should collaborate together).

#explore basic structure:
print("Gh has",len(Gh.nodes(data=True)),"nodes")
print("Gh has",len(Gh.edges(data=True)),"edges")

print("Gh degree centrality:\n")
pp(nx.degree_centrality(Gh)) #dictionary, node:value
Gh_deg_cent=list(nx.degree_centrality(Gh).values()) #only values

#explore degree of centrality with histogram
plt.hist(Gh_deg_cent)
plt.show()

plt.close()

#for betweenness-centrality
list_Gh=list(nx.betweenness_centrality(Gh).values()) #list of betweenness centrality values to plot

plt.hist(list_Gh)
plt.show()
plt.close()

#iterate over the nodes in the GitHub network, calling the node and the dictionary
#set the dictionary item degree per node
for n,d in Gh.nodes(data=True):
    print(n,d) #node, dictionary
    Gh.nodes[n]["degree"]=nx.degree(Gh,n)#set dictionary item degree
    print(n,d)

#this data set is huge, so for subsequent exercises will use 200 nodes

#subset of 200 nodes
Gh_200_nodes=[] #initialize empty list
count=0#initialize counter

for  n, d in Gh.nodes(data=True): #for each node and associated dictionary
    #print(count)
    #print(n,d)
     Gh_200_nodes.append((n,d)) #append tuple of node, dictionary
     count=count+1
     if count==200:
        break
     
Gh_200_nodes=dict(Gh_200_nodes) #turn into graph dictionary format (node:dictionary of attributes)
Gh_200_nodes_keys=list(Gh_200_nodes.keys()) #pull nodes only
u=set(itertools.combinations(Gh_200_node_keys,2)) #generate unique combinations of those nodes- these will be used to
#find the appropriate edges

Gh_200_edges=[]
for s1,s2 in u: #iterating over over each unique set of nodes
    for t in Gh.edges(data=True): #pull the tuple from the edges of the original graph
        if s1 in t and s2 in t: #if both nodes from the combinations are in it
            #print(s1,s2, t,"\n\n")
     ...:   Gh_200_edges.append(t)
#the list of tuples is already the appropriate format for the edges, so leave as is
Gh_200 = nx.Graph() #intialize the empty graph
Gh_200.add_nodes_from(Gh_200_nodes) #add nodes
Gh_200.add_edges_from(Gh_200_edges) #add edges
    
nx.set_node_attributes(Gh_200, Gh_200_edges) #link nodes and edges



#visualization and analysis of GitHub network
#Make a MatrixPlot visualization of the largest connected component subgraph
#with authors grouped by their user group number

#find the largest subgraph
#the .connected components function returns setes of connected nodes, which are by definition subgraphs
#These can be viewed by enclosing in list()

#Return list of subgraphs
Gh_subgraphs = [Gh.subgraph(c) for c in nx.connected_components(Gh_200)]
#Find the largest subgraph
Gh_max_subgraph=sorted(Gh_subgraphs, key=lambda x: len(x))[-1]
#create a matrix plot of the largest subgraph
Gh_max_mp = nv.MatrixPlot(Gh_max_subgraph)
plt.draw()
plt.show()
plt.close()

#view as regular graph format
plt.figure(figsize=(15, 15))
nx.draw(Gh_max_subgraph, with_labels=True)
plt.show()
plt.close()

# view as ArcPlot
a = nv.ArcPlot(Gh_max_subgraph, node_order='degree', node_color='degree')
# Draw the ArcPlot to the screen
plt.draw()
plt.show()
plt.close()

#view as Circos Plot
a = nv.CircosPlot(Gh_max_subgraph, node_order='bipartite', node_grouping='degree', node_color='degree')
# Draw the ArcPlot to the screen
plt.draw()
plt.show()
plt.close()

#practical application, clique analysis
#find number of maximal cliques
len_Gh_200_max_cliques=len(list(nx.find_cliques(Gh_200)))
#find the largest maximal clique
Gh_200_lc=sorted(nx.find_cliques(Gh_200),key=lambda x:len(x))[-1]
Gh_200_lc_sg=Gh_200.subgraph(Gh_200_lc)

# Create the CircosPlot object: c
c = nv.CircosPlot(G_200_lc_sg, node_labels=True)
c.draw()
plt.show()


#final tasks, case studies
#Look for GitHub users that share collaborations with the most number of other users
Gh_deg_cent=nx.degree_centrality(Gh) #returns node:degree centrality dictionary
#sort dictionary so greatest degree of centrality is on top
Gh_deg_cent_sorted = {k: v for k, v in sorted(Gh_deg_cent.items(), key=lambda item: item[1], reverse=True)}
#find the maximum degree of centrality
Gh_deg_cent_max=max(Gh_deg_cent_sorted.values())
#find the most collaborative users
#to determine what "collaborative" means in the context of the data, I am going to look at the distribution in a histogram
plt.hist( Gh_deg_cent_sorted.values())
plt.show()
plt.close()
#roughly a value of 0.0006 cuts off a small subset of the data (~2%)from the majority of data, so that will be my criterion
prolific_users=[u for u in Gh_deg_cent_sorted.keys() if Gh_deg_cent_sorted[u]>=0.0006] #this will return a list of nodes
#find the largest maximal clique in Gh
Gh_lc=sorted(nx.find_cliques(Gh),key=lambda x:len(x))[-1]
#create a subgraph from it
Gh_lc_g=Gh.subgraph(Gh_lc).copy()
display(Gh_lc_g)

#add the neighbors to the subgraph of the largest clique that are removed by one degree of separation
for n in list(Gh_lc_g.nodes()):
    nbrs=Gh.neighbors(n)
    Gh_lc_g.add_nodes_from(nbrs)
    Gh_lc_g.add_edges_from(zip([n]*len(list(Gh.neighbors(n))), Gh.neighbors(n))) #create the edges by making sets of the node and each neighbor

#assign degree centrality
for n in Gh_lc_g.nodes():
    Gh_lc_g.nodes[n]["degree centrality"]=nx.degree_centrality(Gh_lc_g)[n]
#Visualize this network with an ArcPlot sorting the nodes by degree centrality (you can do this using the keyword argument node_order='degree centrality').
# Create the ArcPlot object: a
a = nv.ArcPlot(Gh_lc_g, node_order='degree centrality')

# Draw the ArcPlot to the screen
plt.draw()
plt.show()
plt.close()


# Initialize the defaultdict: recommended
recommended = defaultdict(int)
    for n,d in Gh.nodes(data=True):# for node and associated metadata in the GitHub dataset
        for n1, n2 in combinations(Gh.neighbors(n),2):#calculate combinations of that node and its neighbors
            print ("node: ", n, "neighbor combos: ", n1, n2)
            if not Gh.has_edge(n1,n2): # if the nodes do not share an edge (not connected)
                print("node ",n1, "and node", n2, "do not share an edge!")
                recommended[((n1), (n2))] += 1
                #print(recommended[((n1), (n2))])

all_counts = sorted(recommended.values()) #sort the incremented values to find the top pairs
#returns a list of tuples
top10_pairs = [pair for pair, count in recommended.items() if count > all_counts[-10]] #pull the pairs of users that have the top ten incremented scores
