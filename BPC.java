import ilog.concert.*;
import ilog.cplex.*;

import java.io.*;
import java.util.*;

public final class BranchPriceCut {
	// elements of the graph
	private List<Node> all_nodes;
	private List<Customer> all_customers;
	private Depot source;
	private Depot sink;
	private double [][] distance_matrix;
	private List<Integer> id_external;
	// elements of the search tree
	public List<BBNode> active_nodes = new ArrayList<BBNode>();
	public double lower_bound = Double.MAX_VALUE;
	public double upper_bound = Double.MAX_VALUE;
	public BBNode current_bbNode;
	private List<Integer> incumbent_sol = new ArrayList<Integer>(); //List of ids of paths in best feasible solution
	// elements of the (restricted) masterproblem and pricing problem
	private List<Path> paths = new ArrayList<Path>();
	private List<Path> crowd_paths = new ArrayList<Path>();
	public MasterProblem masterproblem;
	private SPPRC spprc;
	private CCP cuts_subproblem;
	private ArrayList<ArrayList<HashSet<Integer>>> arc_memory;
	// elements of time management
	private static double total_time = 0;
	public Logger logger = new Logger();
	
	// classes for graph model
	private class Node {
		public int id;
		private double x;
		private double y;
		
		public Node(double x, double y) {
			this.id = all_nodes.size();
			this.x = x;
			this.y = y;
			all_nodes.add(this);
		}
		
		public double dist_to_node(Node node_to) {
			return Math.sqrt(Math.pow(this.x-node_to.x, 2)+Math.pow(this.y-node_to.y, 2));
		}
	}
	
	private final class Depot extends Node {
		public Depot(double x, double y) {
			super(x,y);
		}
	}
	
	private final class Customer extends Node{
		private double demand;
		private Set<Integer> ng;
		private Set<Integer> ng_set;
		public Customer(double x, double y, double demand) {
			super(x,y);
			this.demand = demand;
			all_customers.add(this);
			ng = new HashSet<Integer>();
			ng_set = new HashSet<Integer>();
		}
		
		public double demand(){return this.demand;}
	}
	
	// classes for search tree
	private final class BBNode{
		private BBNode parent;
		private boolean arc_branched;
		private boolean one;
		private int i;
		private int j;
		private int[] number_vehicles_lb;
		private int[] number_vehicles_ub;
		private double lb;
		private double percent_int;
		private boolean feasible_bbnode = true;
		
		public BBNode(){
			// constructor for the root node
			// This constructor builds the initial problem without restrictions or branches
			this.parent = null;
			this.arc_branched = false;
			this.number_vehicles_lb = new int[Parameters.K];
			this.number_vehicles_ub = new int[Parameters.K];
			this.number_vehicles_lb[0] = 0;
			this.number_vehicles_ub[0] = Integer.MAX_VALUE;
			for(int k=1; k<Parameters.K; k++){
				this.number_vehicles_lb[k]=0;
				this.number_vehicles_ub[k]=Parameters.max_pref[k];
			}
			this.lb = Double.MAX_VALUE;
			active_nodes.add(this);
		}
		
		public BBNode(BBNode pa, boolean upper,boolean crowd, int bound_value, int type_to_branch_on){
			// constructor for a bbnode when branching on a number of vehicles
			// This constructor is used when the number of vehicles is fractional and we must branch, creating two problems upper and lower.
			this.parent = pa;
			this.lb = pa.lb();
			this.percent_int = pa.percent_int;
			this.arc_branched = false;
			this.number_vehicles_lb = new int[Parameters.K];
			this.number_vehicles_ub = new int[Parameters.K];
			System.arraycopy(pa.number_vehicles_lb, 0, this.number_vehicles_lb, 0, Parameters.K);
			System.arraycopy(pa.number_vehicles_ub, 0, this.number_vehicles_ub, 0, Parameters.K);
			if(!crowd){
				if(upper){
					this.number_vehicles_lb[0] = bound_value;
				} else {
					this.number_vehicles_ub[0] = bound_value;
				}
			} else {
				if(upper) {
					this.number_vehicles_lb[type_to_branch_on] = bound_value;
				} else {
					this.number_vehicles_ub[type_to_branch_on] = bound_value;
				}
			}
			active_nodes.add(this);
		}
		
		public BBNode(int p, int g,boolean isone, BBNode pa){
			// consructor when branching on an arc
			this.parent = pa;
			this.lb = pa.lb();
			this.percent_int = pa.percent_int;
			this.arc_branched = true;
			this.i = p;
			this.j = g;
			this.one = isone;
			this.number_vehicles_lb = new int[Parameters.K];
			this.number_vehicles_ub = new int[Parameters.K];
			System.arraycopy(pa.number_vehicles_lb, 0, this.number_vehicles_lb, 0, Parameters.K);
			System.arraycopy(pa.number_vehicles_ub, 0, this.number_vehicles_ub, 0, Parameters.K);
			active_nodes.add(this);
		}
		
		public int i() {return this.i;}
		public int j() {return this.j;}
		public double lb() {return lb;}
		public boolean feasible_bbnode() {return feasible_bbnode;}
	}
	
	// classes for masterproblem
	private final class Path {
		private int id;
		private ArrayList<Customer> customers;
		//private int[] customers_id;
		private IloNumVar y;
		private double cost;
		private int type;
		private int preference;
		private int[][] b_coeffs;
		private int[] a_coeffs;
		
		public Path(ArrayList<Integer> stops_new_path, int k, int s) {
			// stops_new_path is the list of ids and includes the source and the sink
			this.type = k;
			this.preference = s;
			this.customers = new ArrayList<Customer>();
			a_coeffs = new int[all_nodes.size()];
			b_coeffs = new int[all_nodes.size()][all_nodes.size()];
			for(int i=1; i<stops_new_path.size()-1; i++) {
				customers.add(all_customers.get(stops_new_path.get(i)-1));
				a_coeffs[stops_new_path.get(i)]++;
			}
			this.cost = calculateCost();
			for(int i=0; i<this.customers.size()-1; i++){
				b_coeffs[this.customers.get(i).id][this.customers.get(i+1).id]++;
			}
			//take into account first and last arc with the source and sink:
			this.b_coeffs[source.id][this.customers.get(0).id]++;
			this.b_coeffs[this.customers.get(this.customers.size()-1).id][sink.id]++;
			this.id = paths.size();
			paths.add(this);
			if(k >= 1) {crowd_paths.add(this);}
		}
		
		public Path(double cost) {
			// special constructor for the dummy path: uses no arc magically
			this.type = 0;
			this.preference = 0;
			this.cost = cost;
			this.customers = new ArrayList<Customer>(all_customers);
			this.id = paths.size();
			paths.add(this);
			this.b_coeffs = new int[all_nodes.size()][all_nodes.size()];
			this.a_coeffs = new int[all_nodes.size()];
			for(int i=0; i<all_nodes.size(); i++){
				this.a_coeffs[i]=1;
			}
		}
		
		private double calculateCost() {
			int k = this.type;
			int s = this.preference;
			double temp_cost = Parameters.fixed_cost[k][s];
			double distance = 0.0;
			for(int i=0; i<this.customers.size()-1;i++){
				distance += distance_matrix[this.customers.get(i).id][this.customers.get(i+1).id];
			}
			distance += distance_matrix[source.id][this.customers.get(0).id];
			distance += distance_matrix[this.customers.get(this.customers.size()-1).id][sink.id];
			temp_cost += Parameters.variable_cost[k][s]*distance;
			//if(k>=1) {
			//	double v_ks = Parameters.variable_cost[k][s];
			//	if (customers.size()>0) {
			//		temp_cost = v_ks*(distance_matrix[source.id][customers.get(0).id]) + Parameters.fixed_cost[k][s];
			//		for (int i=1; i<customers.size(); i++) {
			//			temp_cost += v_ks*(distance_matrix[customers.get(i-1).id][customers.get(i).id]);
			//		}
			//		temp_cost += Parameters.penalty*Parameters.V[0]*Parameters.recourse_prob[k][s]*(distance_matrix[customers.get(customers.size()-1).id][sink.id]);
			//	}
			//} else {
			//	double v = Parameters.variable_cost[0][0];
			//	if (customers.size() > 0) {
			//		temp_cost = v*(distance_matrix[source.id][customers.get(0).id]) + Parameters.fixed_cost[0][0];
			//		for (int i=1; i<customers.size(); i++) {
			//			temp_cost += v*(distance_matrix[customers.get(i-1).id][customers.get(i).id]);
			//		}
			//		temp_cost += v*(distance_matrix[customers.get(customers.size()-1).id][sink.id]);
			//	}
			//}
			return temp_cost;
		}
		
		private int a(Customer customer) {return a_coeffs[customer.id];}
		private double b(int i, int j){return (double) this.b_coeffs[i][j];}
		
		private boolean feasible_path() {
			double cap = 0;
			for (Customer c: customers) {
				cap += c.demand;
				if(cap>Parameters.Q[this.type]) {System.out.println("Not feasible path"); return false;}
			}
			return true;
		}
		
		public void displayInfo() {
			this.feasible_path();
			System.out.println("cost: " +this.cost);
			for (Customer c: this.customers) {System.out.print(c.id + " ");}
			System.out.println("");
		}
	}
		
	public final class MasterProblem {
		public IloCplex cplex;
		private IloObjective total_cost;
		private IloRange[] rows_customers;
		private IloRange[][] rows_preference;
		private IloRange[] rows_number_vehicles;
		private ArrayList<IloNumVar> number_vehicles_var;
		private double[] dual_number_vehicles;
		private ArrayList<IloRange> RCCs = new ArrayList<IloRange>();
		private ArrayList<ArrayList<Integer>> RCC_sets = new ArrayList<ArrayList<Integer>>();
		private double[][] dual_arcs;
		private double[] pi;
		private double [][] mu;
		public double lastObjValue;
		
		public MasterProblem() {
			createModel();
			createDefaultPaths();
			Parameters.configureCplex(this);
			this.cplex.setOut(null);
		}

		private void createModel() {
			mu = new double [Parameters.K][];
			for(int k=1;k<Parameters.K;k++){
				mu[k] = new double[Parameters.max_pref[k]+1];
			}

			rows_preference = new IloRange[Parameters.K][];
			rows_preference[0] = new IloRange[1];
			for(int k=1;k<Parameters.K;k++){
				rows_preference[k] = new IloRange[Parameters.max_pref[k]];
			}
			try{
				cplex = new IloCplex();
				total_cost = cplex.addMinimize();

				// all customers must be visited at least once (the indice 0 stays empty)
				rows_customers = new IloRange[all_customers.size()+1];
				for (Customer c: all_customers){
					rows_customers[c.id] = cplex.addRange(1, Double.MAX_VALUE, "cust "+c.id);
				}
				// for each priority only one route is allowed
				for(int k = 1; k < Parameters.K; k++) {
					for(int s=1; s<= Parameters.max_pref[k]; s++){
						rows_preference[k][s-1] = cplex.addRange(-1.0, 0, "preference " + k + " " + s);
					}
				}
				// constraint to branch on the numbers of vehicles: 0 is the total and other are for each category 1,...,K-1
				rows_number_vehicles = new IloRange[Parameters.K];
				number_vehicles_var = new ArrayList<IloNumVar>(Parameters.K);
				rows_number_vehicles[0] = cplex.addRange(0 , 0, "constraint total nb of vehicles");
				IloColumn new_column = cplex.column(total_cost, 0);
				new_column = new_column.and(cplex.column(rows_number_vehicles[0],-1.0));
				number_vehicles_var.add(cplex.numVar(new_column, 0, Double.MAX_VALUE, "total nb of vehicles "));
				for(int k=1;k<Parameters.K;k++){
					rows_number_vehicles[k] = cplex.addRange(0, 0, "nb crowd-vehicles "+k);
					IloColumn new_column2 = cplex.column(total_cost, 0);
					new_column2 = new_column2.and(cplex.column(rows_number_vehicles[k],-1.0));
					number_vehicles_var.add(cplex.numVar(new_column2, 0, Parameters.max_pref[k], "crowd-vehicles "+k));
				}
			}
			catch (IloException e) {
				System.err.println("Concert exception caught: " + e);
			}
		}

		private void createDefaultPaths() {
			double dummy_cost = Parameters.F[0]*Parameters.num_customers;
			for (Customer c : all_customers) {
				dummy_cost+= distance_matrix[c.id][source.id]*2;
				ArrayList<Integer> new_path = new ArrayList<Integer>();
				new_path.add(source.id);
				new_path.add(c.id);
				new_path.add(sink.id);
				addNewColumn(new Path(new_path, 0, 0));
			}
			try {
				Path path = new Path(dummy_cost);
				//create dummy column
				IloColumn new_column = cplex.column(total_cost, dummy_cost);
				// that visits all customers once
				for (Customer c : all_customers) {
					new_column = new_column.and(cplex.column(rows_customers[c.id], 1.0));
				}
				path.y = cplex.numVar(new_column, 0, 1, "y." +path.id );
			} catch (IloException e) {
				System.err.println("Concert exception caught: " + e);
			}
		}
		
		private void addNewColumn(Path path) {
			try {
				IloColumn new_column = cplex.column(total_cost, path.cost);
				for (Customer c : all_customers) {
					if(path.a(c)>0){
						new_column = new_column.and(cplex.column(rows_customers[c.id],path.a(c)));
					}
				}
				if(path.type>=1) {
					//only one route per priority and category
					new_column = new_column.and(cplex.column(rows_preference[path.type][path.preference-1], -1.0));
					//count in its type of vehicle variable
					new_column = new_column.and(cplex.column(rows_number_vehicles[path.type], 1.0));
				}
				//add to total vehicles variable
				new_column = new_column.and(cplex.column(rows_number_vehicles[0], 1.0));
				path.y = cplex.numVar(new_column, 0, 1, "y."+path.id);

				// add to the existing cuts if needed
				if(!RCC_sets.isEmpty()){
					for(int l=0;l<RCCs.size();l++){
						double coeff=0;
						for(int i: RCC_sets.get(l)){
							for(int j=0; j<all_nodes.size();j++){
								if(!RCC_sets.get(l).contains(j)){
									coeff+=path.b(j,i);
									coeff+=path.b(i,j);
								}
							}
						}
						if(coeff>0){
						cplex.setLinearCoef(RCCs.get(l), coeff, path.y);
						}
					}
				}
			}
			catch (IloException e) {
				System.err.println("Concert exception caught: " + e);
			}
		}
		
		private void addNewRCC(ArrayList<Integer> cut_set, double rhs) {
			// cut_set is a list of customers id
			System.out.println("adding a cut");
			System.out.println(cut_set);
			System.out.println(rhs);
			try {
				// initialize the new constraint
				int index = masterproblem.RCCs.size();
				IloRange new_cut = cplex.addRange(rhs, Double.MAX_VALUE, "cut "+index);
				// for each existing route, compute its coefficient in the cut
				for(Path p: paths){
					double coeff = 0;
					for(int id: cut_set){
						for(Customer c2: all_customers){
							if(!cut_set.contains(c2.id)){
								coeff+=p.b(c2.id,id);
								coeff+=p.b(id,c2.id);
							}
						}
						// take into account arcs from the source and to the sink
						coeff+=p.b(source.id, id);
						coeff+=p.b(id, sink.id);
					}
					
					if(coeff>0){
						cplex.setLinearCoef(new_cut, coeff, p.y);
					}
				}
				RCC_sets.add(cut_set);
				RCCs.add(new_cut);
			} catch (IloException e) {
				System.err.println("Concert exception caught: " + e);
			}
		}
		
		private boolean solveRelaxation() {
			try {
				if (cplex.solve()) {
					saveDualValues();
					lastObjValue = cplex.getObjValue();
					return true;
				} else {
					return false;
				}
			}
			catch (IloException e) {
				System.err.println("Concert exception caught: " + e);
				return false;
			}
		}
		
		private void saveDualValues() {
			this.dual_number_vehicles = new double[Parameters.K];
			this.pi = new double[all_nodes.size()];
			this.dual_arcs = new double[all_nodes.size()][all_nodes.size()];
			try {
				dual_number_vehicles[0] = cplex.getDual(rows_number_vehicles[0]);
				for(int k=1;k<Parameters.K;k++){
					dual_number_vehicles[k] = cplex.getDual(rows_number_vehicles[k]);
				}
				for (Customer c : all_customers) {
					pi[c.id] = cplex.getDual(rows_customers[c.id]);
				}
				for(int k = 1; k < Parameters.K; k++) {
					for (int s = 1; s<=Parameters.max_pref[k];s++) {
						mu[k][s] = cplex.getDual(rows_preference[k][s-1]);
					}
				}
				if(!RCC_sets.isEmpty()){
					for(int i=0; i<all_nodes.size(); i++){
						for(int j=0; j<all_nodes.size(); j++){
							for(int l=0; l<RCC_sets.size(); l++){
								if((RCC_sets.get(l).contains(i) && !RCC_sets.get(l).contains(j))||(!RCC_sets.get(l).contains(i) && RCC_sets.get(l).contains(j))){
									dual_arcs[i][j]+=cplex.getDual(RCCs.get(l));
								}
							}
						}
					}
				}
			}
			catch (IloException e) {
				System.err.println("Concert exception caught: " + e);
			}
		}
		
		private void updateMP() {
			try {
				//set bound on number of vehicles
				for(int k=0; k<Parameters.K;k++){
					masterproblem.number_vehicles_var.get(k).setLB(current_bbNode.number_vehicles_lb[k]);
					masterproblem.number_vehicles_var.get(k).setUB(current_bbNode.number_vehicles_ub[k]);
				}
				// reset bounds for route variables
				for(Path p: paths){
					p.y.setUB(1.0);
				}
				BBNode rec = current_bbNode;
				while (rec.parent != null) {
					if(rec.arc_branched) {
						if(rec.one && rec.i != rec.j) {
							if(rec.i != source.id && rec.j != sink.id) {
								for(Path p: paths){
									if(p.b(rec.j,rec.i)>0){p.y.setUB(0.0);}
								}
							}
							if (rec.i != source.id) {
								for(Node c: all_nodes) {
									if (c.id!=rec.j && c.id!= rec.i) {
										for(Path p: paths){
											if(p.b(rec.i,c.id)>0){p.y.setUB(0.0);}
										}
									}
								}
							}
							if(rec.j != sink.id){
								for(Node c: all_nodes){
									if (c.id!=rec.i && c.id!= rec.j) {
										for(Path p: paths){
											if(p.b(c.id,rec.j)>0){p.y.setUB(0.0);}
										}
									}
								}
							}
						} else {
							for(Path p: paths){
								if(p.b(rec.i,rec.j)>0){p.y.setUB(0.0);}
							}
						}
					}
					rec = rec.parent;
				}
				
			} catch (IloException e) {
				System.err.println("Concert exception caught: " + e);
			}
		}
		
		public void displaySolution(boolean MIP) {
			try {
				BranchPriceCut.total_time = logger.timeStamp();
				System.out.println("elpased time: "+total_time+ " s");
				double t_cost  = 0 ;
				int[] nb_vehicles = new int[Parameters.K];
				if (MIP) {
					for (Path path : paths) {
						if (cplex.getValue(path.y) > 0.99999) {
							path.displayInfo();
							nb_vehicles[path.type]+=1;
							t_cost += path.cost;
						}
					}
				} else {
					System.out.println("Best feasible solution:");
					for (int p : incumbent_sol) {
						Path path = paths.get(p);
						nb_vehicles[path.type]+=1;
						if(path.type >= 1) {
							System.out.println("CV "+path.type+" "+path.preference);
							path.displayInfo();
						}else {
						System.out.println("PV");
						path.displayInfo();}
						t_cost += path.cost;
					}
					for(int k=0; k<Parameters.K;k++){
						System.out.println("vehicles of type "+k+" used: "+nb_vehicles[k]);
					}
				}
				System.out.println("total cost: " +t_cost);
				if(active_nodes.size()>0) {
					//System.out.println("Not optimal or optimality not proved");
					System.out.println(((float)(Math.round(10000*(t_cost -lower_bound)/lower_bound))/100) + "%");
				}else {System.out.println("Optimal");
					System.out.println(0.00 + "%");}
				System.out.println(BranchPriceCut.total_time);
			}
			catch (IloException e) {
				System.err.println("Concert exception caught: " + e);
			}
		}
	}
	
	/////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////// SHORTEST PATH PROBLEM ////////////////////////////////////////////
	/////////////////////////////////////////////////////////////////////////////////////////////////////
	
	public final class SPPRC {
		private List<List<List<Label>>> matrix;
		private int Cap;

		private class Label{
			private Label previous;
			private int node_id;
			//private double load;
			private double distance;
			private double rho; // cumulative dual variables for visited customers and cuts
			private Set<Integer> ng_set;
			private double partial_redco;

			public Label(int c_id) {
				// constructor for the initial depot label
				this.node_id = c_id;
				//this.load = 0;
				this.distance = 0;
				this.partial_redco = 0;
				this.rho = 0;
				this.ng_set = new HashSet<Integer>();
				this.previous = null;
			}

			public Label (Label L2, int next_node_id) {
				this.node_id = next_node_id;
				this.previous = L2;
				//load_REF(L2, next_node_id);
				distance_REF(L2, next_node_id);
				set_REF(L2, next_node_id);
				dual_REF(L2, next_node_id);
			}

			//private void load_REF(Label L2, int next_node_id){
			//	this.load = L2.load + all_customers.get(next_node_id-1).demand();
			//}

			private void distance_REF(Label L2, int next_node_id) {
				this.distance = L2.distance + distance_matrix[L2.node_id][next_node_id];
			}

			private void set_REF(Label L1, int next_node_id) {
				this.ng_set = new HashSet<Integer>();
				this.ng_set.addAll(L1.ng_set);
				this.ng_set.retainAll(all_customers.get(next_node_id-1).ng);
				//this.ng_set.retainAll(arc_memory.get(L1.node_id).get(next_node_id));
				this.ng_set.add(next_node_id);
			}

			private void dual_REF(Label L1, int next_node_id) {
				this.rho = L1.rho ;
				this.rho += masterproblem.pi[next_node_id];
				this.rho += masterproblem.dual_arcs[L1.node_id][next_node_id];
				this.partial_redco = this.distance - this.rho;
			}
		}

		private final class path_vehicle{
			List<Integer> customers_id;
			int type;
			int preference;
			double value;

			private path_vehicle(Label l, int k, int s, double val){
				this.type = k;
				this.preference = s;
				customers_id = new ArrayList<Integer>(label_to_list(l));
				value = val;
			}
		}

		public SPPRC(int Q) {
			this.matrix = new ArrayList<List<List<Label>>>(Q+1);
			this.Cap = Q;
			// matrix initialization
			for(int q=0; q<=Q; q++) {
				matrix.add(new ArrayList<List<Label>>(all_customers.size()+1));
				for(int i=0; i<=all_customers.size(); i++) {
					this.matrix.get(q).add(new ArrayList<Label>());
				}
			}
		}

		private ArrayList<Integer> label_to_list(Label L){
			// transforms a label into a list of integers
			ArrayList<Integer> path = new ArrayList<Integer>();
			Label p = L;
			while(p != null) {
				if(p.node_id == source.id) {break;}
				path.add(p.node_id);
				p = p.previous;
			}
			Collections.reverse(path);
			return path;
		}
		
		private boolean single_DP(boolean heuristic, int iter) {
			List<path_vehicle> neg_columns = new ArrayList<path_vehicle>();
			double best_rc = 0.0;
			int deleted = 0;
			double bound = -0.000001;
			this.matrix.get(0).get(0).add(new Label(source.id));
			//start dynamic program
			for(int q = 0; q <=this.Cap; q++) {
				if(neg_columns.size()>9) {break;}
				for(int i=0; i<all_customers.size(); i++) {
					if(neg_columns.size()>9) {break;}
					int di = (int)all_customers.get(i).demand();
					if(q-di >= 0) {
						for(int j=0; j<all_customers.size(); j++) {
							if(neg_columns.size()>9) {break;}
							for(int l2=0; l2<matrix.get(q-di).get(j).size(); l2++) {
								if(neg_columns.size()>9) {break;}
								if(feasible_label(matrix.get(q-di).get(j).get(l2),i)){
									Label L1 = new Label(matrix.get(q-di).get(j).get(l2), all_customers.get(i).id);
									boolean insertL1 = true;
									for(int l_1=0;l_1<matrix.get(q).get(i).size();l_1++){
										if(neg_columns.size()>9) {break;}
										if(dominates(L1, matrix.get(q).get(i).get(l_1), heuristic, iter) ) {
											matrix.get(q).get(i).remove(l_1);
											l_1--;
										}else if(dominates(matrix.get(q).get(i).get(l_1),L1,heuristic, iter)) {
											insertL1 = false;
											break;
										}
									}
									if(insertL1) {
										matrix.get(q).get(i).add(L1);
										if(extend_arc(L1.node_id, sink.id)) {
											for(int k=0; k<Parameters.K; k++) {
												if(q > Parameters.Q[k]) {break;}
												for(int s=0; s<=Parameters.max_pref[k]; s++) {
													if((k==0 && s>0) || (k>0 && s==0)) {
														continue;
													} else {
														double temp_reducedcost = reduced_cost(L1,k,s);
														if(temp_reducedcost<bound) {
															if(temp_reducedcost<best_rc-0.0001) {
																best_rc = temp_reducedcost;
																neg_columns.add(new path_vehicle(L1,k,s,temp_reducedcost));
																if(neg_columns.size()>10 && deleted<300) {deleted += 1; neg_columns.remove(0);}
															}
														}
													}
												}
											}
										}
									}
								}
							}
						}
					}
				}
			}
			int added = 0;
			for (int i = 0; i < neg_columns.size(); i ++) {
				if(isNG(neg_columns.get(i).customers_id)) {
					added += 1;
					ArrayList<Integer> stops_new_path = new ArrayList<Integer>();
					stops_new_path.add(source.id);
					stops_new_path.addAll(neg_columns.get(i).customers_id);
					stops_new_path.add(sink.id);
					//System.out.println(stops_new_path+" "+neg_columns.get(i).type+" "+neg_columns.get(i).preference);
					BranchPriceCut.this.masterproblem.addNewColumn(new Path(stops_new_path, neg_columns.get(i).type, neg_columns.get(i).preference));
				}
			}
			if(neg_columns.size()>0) {
				if(added == 0) {
					int cheapest =0;
					double cheap = 0.0;
					for (int i=0; i<neg_columns.size(); i++) {
						if(cheap>neg_columns.get(i).value) {
							cheap=neg_columns.get(i).value;
							cheapest=i;
						}
					}
					forbidden_cycle(neg_columns.get(cheapest).customers_id);
				}
				return true;
			}else{
				return false;
			}
		}

		private boolean extend_arc(int i, int j ) {
			if(i == j) {return false;}
			BBNode bb = current_bbNode;
			while(bb.parent != null) {
				if(bb.arc_branched) {
					if(bb.i() == i) {
						if(bb.one) {
							if(bb.j() == j) {
								return true;
							}else {
								if(bb.i()!= source.id) {
									return false;
								}
							}
						}else {
							if(bb.j() == j) {
								return false;
							}
						}
					}
					else if(bb.j() == j) {
						if(bb.one) {
							if(bb.j() != sink.id) {
								return false;
							}
						}
					}
				}
				bb = bb.parent;
			}
			return true;
		}

		private boolean feasible_label(Label L2,int i) {
			// i is the index of the next customer in the list all_customers
			if(L2.ng_set.contains(all_customers.get(i).id)) {return false;}
			if(!extend_arc(L2.node_id, all_customers.get(i).id)) {return false;}			
			return true;
		}

		private boolean isNG(List<Integer> cy) {
			// cy is a list of customer ids
			boolean isng = true;
			for(int step = 2; step < cy.size();step ++) {
				for(int i = 0; i < cy.size()-step; i++) {
					if(cy.get(i) == cy.get(i+step)){
						boolean found = true; 
						if(step == 2) {
							//System.out.println("---------- Two cycle found isNG");
							return false;
						}else {
							//System.out.println("---------- Long cycle found isNG");
							for(int j = i; j < i + step ; j ++) {
								if(!all_customers.get(cy.get(j)-1).ng_set.contains(cy.get(i))) {
									found = false;
									break;
								}
							}
						}
						if (found) {
							return false;
						}
					}
					
				}
			}
			return isng;
		}

		private boolean forbidden_cycle(List<Integer> pv){
			// pv is a list of customers ids
			//System.out.println("Find cycle begins with path size = " + l.path_r.size());
			boolean found = false;
			for(int step=2; step<=all_customers.size(); step++) {
				for(int i=0; i<pv.size()-step; i++) {
					if(pv.get(i) == pv.get(i+step)){
						if(step == 2) {
							//cycle of length 2 found
							//System.out.print("---------- Two cycle found in find cycle ");
							all_customers.get(pv.get(i)-1).ng.add(pv.get(i+1));
							all_customers.get(pv.get(i+1)-1).ng.add(pv.get(i));
							found =  true;
						}else {
							//System.out.print("---------- Long cycle found in find cycle " + step + " Subp " + this.type);
							boolean ng_cycle = true;
							for(int j=i; j<i+step; j++) {
								if(!ng_cycle) {break;}
								if(!all_customers.get(pv.get(j)-1).ng_set.contains(pv.get(i))) {
									ng_cycle = false;
									break;
								}
							}
							if(ng_cycle) {
								//System.out.println("---------- ng cycle ");
								found = true;
								for(int j=i; j<i+step; j++) {
									if(!all_customers.get(pv.get(j)-1).ng.contains(pv.get(i))) {
										all_customers.get(pv.get(j)-1).ng.add(pv.get(i));
									}
								}
							}
						}
						//boolean ng_cycle=true;
						//for(int j=i; j<i+step; j++) {
						//	if(!ng_cycle) {break;}
						//	if(!all_customers.get(pv.get(j)-1).ng_set.contains(pv.get(i))) {
						//		ng_cycle = false;
						//		break;
						//	}
						//}
						//if(ng_cycle) {
						//	found = true;
						//	for(int j1=i; j1<i+step; j1++) {
						//		for(int j2=i; j2<i+step; j2++){
						//			if(j1!=j2){
						//				arc_memory.get(pv.get(j1)).get(pv.get(j2)).add(pv.get(i));
						//			}
						//		}
						//	}
						//}
					}
				}
			}
			return found;
		}

		private boolean dominates(Label L1, Label L2,boolean heuristic, int iter) {
			// returns true if L1 dominates L2
			boolean dominates = false;
			if(L1.partial_redco <= L2.partial_redco) {//smaller reduced cost
				if(iter == 0 ) {return true;}
				if(iter == 1 ) {return true;}
				if(L1.distance <= L2.distance) {
					if(iter == 2 ) {return true;}
					if(heuristic) {return true;}
					if(L2.ng_set.containsAll(L1.ng_set)) {
						dominates = true;
					}
				}
			}
			return dominates;
		}

		private double reduced_cost(Label L, int k, int s) {
			// compute the reduced cost of a route created with label L
			double temp_reducedcost=Parameters.fixed_cost[k][s];;
			temp_reducedcost += Parameters.variable_cost[k][s]*(L.distance + distance_matrix[L.node_id][sink.id]);
			temp_reducedcost -= L.rho;
			temp_reducedcost -= masterproblem.dual_arcs[L.node_id][sink.id];
			temp_reducedcost -= masterproblem.dual_number_vehicles[0];
			if(k>=1){
				temp_reducedcost += masterproblem.mu[k][s];
				temp_reducedcost -= masterproblem.dual_number_vehicles[k];
			}
			return temp_reducedcost;
		}
	}
	
/////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////// END SHORTEST PATH PROBLEM END //////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////

	private final class CCP{
		// class for the subproblem of finding a cut using the connected components heuristic
		private boolean[][] graph = new boolean[all_nodes.size()][all_nodes.size()];
		private int[] connected_compo = new int[all_nodes.size()];
		private double[][] arc_values = new double[all_nodes.size()][all_nodes.size()];
		
		public CCP() {
			//compute arc vals
			try {
				for(Path p: paths){
					double path_val = BranchPriceCut.this.masterproblem.cplex.getValue(p.y);
					if(path_val>0.0001){
						for(int i=0; i<all_nodes.size();i++){
							for(int j=0; j<all_nodes.size();j++){
								if(i!=j){
									this.arc_values[i][j] += (p.b(i,j)*path_val);
								}
							}
						}
					}
				}
			} catch (IloException e) {
				System.err.println("Concert exception caught: " + e);
			}
			// build the graph according to arc vals
			for(int i=0;i<all_nodes.size();i++){
				connected_compo[i]=-1;
				for(int j=0;j<all_nodes.size();j++){
					if(j!=i){
						double sum_e = 0;
						sum_e += arc_values[i][j];
						sum_e += arc_values[j][i];
						if(sum_e > 0.0001) {
							graph[i][j]=true;
							graph[j][i]=true;
						}
					}
				}
			}
		}
		
		private boolean search_cuts() {
			//System.out.println("looking for a cut");
			int count_cc = 0;
			for(Customer c: all_customers) {
				if (connected_compo[c.id]<0) {
					DFS(c.id, count_cc);
					count_cc++;
				}
			}
			int best_cut = 0;
			double best_cut_slack = 0.00001;
			boolean cut_found = false;
			for(int l=0; l<count_cc;l++) {
				double q_S = 0;
				double sum_x = 0;
				for(Customer c: all_customers) {
					if (connected_compo[c.id]==l) {
						q_S+=c.demand;
						sum_x += arc_values[source.id][c.id];
						sum_x += arc_values[c.id][sink.id];
					}
				}
				// check the RCI
				if(2*Math.ceil(q_S/Parameters.Q[0])-sum_x>best_cut_slack) {
					best_cut_slack = 2*Math.ceil(q_S/Parameters.Q[0])-sum_x;
					cut_found=true;
					best_cut = l;
				}
			}	
			// add most violated cut
			if (cut_found) {
				ArrayList<Integer> cut_set = new ArrayList<Integer>();
				double q_S = 0;
				for(Customer c: all_customers) {
					if(connected_compo[c.id]==best_cut) {
						q_S+= c.demand;
						cut_set.add(c.id);
					}
				}
				double rhs = 2*Math.ceil(q_S/Parameters.Q[0]);
				BranchPriceCut.this.masterproblem.addNewRCC(cut_set, rhs);
			}
			return cut_found;
		}
		
		private void DFS(int id, int cc) {
			connected_compo[id] = cc;
			for(Customer c: all_customers) {
				if(graph[id][c.id] && connected_compo[c.id]<0) {
					DFS(c.id, cc);
				}
			}
		}
	}
	
	public BranchPriceCut(String instance) {
		//read the information for the instance for each customer
		ReadData(instance);
		this.distance_matrix = new double [Parameters.num_customers+2][Parameters.num_customers+2];
		//fill cost matrix with the distance between customers.
		for (int i=0; i<all_nodes.size(); i++) {
			for (int j=0; j<all_nodes.size();j++) {
				distance_matrix[i][j] = all_nodes.get(i).dist_to_node(all_nodes.get(j));
			}
		}
		//create initial node
		this.current_bbNode = new BBNode();
		//get the nearest neighbors list for all customers
		buildNg();
		//Create restricted master problem and sub problems
		masterproblem = new MasterProblem();
		spprc = new SPPRC((int)Parameters.Q[0]);
	}
	
	private void ReadData(String instance) {
		try {
			File file = new File("/home/instances/" + instance);
					 	BufferedReader br = new BufferedReader(new FileReader(file)); 
			String st;
			int default_capacity;
			// skip first 3 lines
			for(int i=0; i<3; i++) {st = br.readLine();}
			// read dimension (number of nodes, including depot)
			st = br.readLine();
			String[] parse_dim = st.split(" ");
			int number_nodes = Integer.parseInt(parse_dim[2]);
			// initialize graph objects to the correct size
			all_customers = new ArrayList<Customer>(15-1);
			all_nodes = new ArrayList<Node>(15+1);
			id_external = new ArrayList<Integer>(15+1);
			// skip next line
			st = br.readLine();
			// read default capacity (capacity of professional vehicles)
			st = br.readLine();
			String[] parse_cap = st.split(" ");
			default_capacity = Integer.parseInt(parse_cap[2]);
			// Set parameters of the problem
			Parameters.param(3, default_capacity,15-1);
			// read nodes information
			int[] id_ext = new int[number_nodes];
			double[] xcoord = new double[number_nodes];
			double[] ycoord = new double[number_nodes];
			double[] demand = new double[number_nodes];
			st = br.readLine();
			for(int i=0;i<number_nodes;i++) {
				st = br.readLine();
				String[] parse_st = st.split(" ");
				id_ext[i]=Integer.parseInt(parse_st[1]);
				xcoord[i]=(double)Integer.parseInt(parse_st[2]);
				ycoord[i]=(double)Integer.parseInt(parse_st[3]);
			}
			st = br.readLine();
			for(int i=0;i<number_nodes;i++) {
				st = br.readLine();
				String[] parse_st = st.split(" ");
				demand[i]=(double)Integer.parseInt(parse_st[1]);
			}
			// create graph objects: depot has nodes 0 and n+1, n number of customers
			source = new Depot(xcoord[0],ycoord[0]);
			for(int i=1;i<15;i++) {
				new Customer(xcoord[i], ycoord[i], demand[i]);
				id_external.add(id_ext[i]);
			}
			sink = new Depot(xcoord[0], ycoord[0]);
			br.close();
		}
		catch (Exception ex) {
			ex.printStackTrace();
		}
	}
	
	private void buildNg() {
		for (Customer c1: all_customers) {
			c1.ng_set.add(c1.id);
			List<Integer> neighbours_id = new ArrayList<Integer>();
			// order customers from closest to further for each customer
			for (Customer c2: all_customers) {
				if(c1.id!=c2.id) {
					if(neighbours_id.size()==0) {neighbours_id.add(c2.id);}
					 else {
						boolean inserted=false;
						for(int rank=0; rank<neighbours_id.size(); rank++) {
							if(distance_matrix[c1.id][neighbours_id.get(rank)]>distance_matrix[c1.id][c2.id]){
								neighbours_id.add(rank, c2.id);
								inserted =true;
								break;
							}
						}
						if(!inserted) {neighbours_id.add(c2.id);}
					}
				}
			}
			// resize to delta_ng size
			for(int p=0; p<neighbours_id.size(); p++) {
				if(p<Parameters.delta_ng) {
					c1.ng_set.add(neighbours_id.get(p));
				}else {
					break;}
			}
		}
		arc_memory = new ArrayList<ArrayList<HashSet<Integer>>>(all_nodes.size());
		for(int i=0; i<all_nodes.size(); i++){
			arc_memory.add(new ArrayList<HashSet<Integer>>(all_nodes.size()));
			for(int j=0; j<all_nodes.size(); j++){
				arc_memory.get(i).add(new HashSet<Integer>(all_customers.size()));
			}
		}
		// arc_memory initialization
		for(Customer c: all_customers){
			double best = Double.MAX_VALUE;
			int nearest_id = c.id;
			for(Customer c2: all_customers){
				if(c2.id!=c.id && distance_matrix[c.id][c2.id]<best){
					best = distance_matrix[c.id][c2.id];
					nearest_id = c2.id;
				}
			}
			arc_memory.get(c.id).get(nearest_id).add(c.id);
			arc_memory.get(c.id).get(nearest_id).add(nearest_id);
			arc_memory.get(nearest_id).get(c.id).add(c.id);
			arc_memory.get(nearest_id).get(c.id).add(nearest_id);
		}
	}

	public void select_BBNode(int strategy) {
		// the list of bbnodes has been checked non empty
		if(strategy == 0) {
			// select bbnode with lowest lower bound
			int next = 0;
			double best_bound = Double.MAX_VALUE;
			for(int i = 0; i < active_nodes.size();i++) {
				//System.out.print(active_nodes.get(i).lb+" ");
				if(best_bound > active_nodes.get(i).lb) {
					best_bound = active_nodes.get(i).lb;
					next = i;
				}
			}
			//System.out.println();
			// change current bbnode for the selected bbnode and update global lower bound if necessary
			this.current_bbNode = active_nodes.get(next);
			this.lower_bound = Math.min(best_bound, this.upper_bound);
		} else if(strategy==1){
			// select bbnode with best integrity
			int next = 0;
			double best_integrity = 0.0;
			for(int i = 0; i < active_nodes.size();i++) {
				double integrity = active_nodes.get(i).percent_int;
				if(best_integrity < integrity) {
					best_integrity = integrity;
					next = i;
				}
			}
			// change current bbnode
			this.current_bbNode = active_nodes.get(next);
		} else {
			// default strategy: queue
			this.current_bbNode = active_nodes.get(0);
		}
	}
	
	public void runColumnGeneration() {
		boolean new_column_found= true;
		boolean at_least_one = false;
		// update the master problem with the info of the current bbnode
		masterproblem.updateMP();
		do {
			if(!masterproblem.solveRelaxation()) {
				System.out.println("NO SOLUTION FOUND");
				break;
			}
			spprc = new SPPRC((int)Parameters.Q[0]);
			for(int i = 0; i <= 3; i++) {
				new_column_found = spprc.single_DP(false,i);
				if(new_column_found) {
					at_least_one = true;
					break;
				}
			}
			if(!new_column_found && at_least_one) {
				cuts_subproblem = new CCP();
				boolean new_cut_found = cuts_subproblem.search_cuts();
				if(new_cut_found){new_column_found=true; at_least_one=false;}
			}
		} while (new_column_found);
		current_bbNode.lb = masterproblem.lastObjValue;
		// check feasibility of the relaxation
		if(!masterproblem.solveRelaxation()) {
			current_bbNode.feasible_bbnode = false;
			System.out.println("a non feasible bbnode");
		// if feasible, check if lower bound of the masterprobem should be updated
		} else if(masterproblem.lastObjValue + 0.00001 < lower_bound && current_bbNode.feasible_bbnode()) {
			lower_bound = masterproblem.lastObjValue;
		}
	}
	
	public boolean prune_bbnode(BBNode b) {
		// if not feasible, remove the node
		if(!b.feasible_bbnode()){
			active_nodes.remove(b);
			return true;
		}
		// if this bbnode lb is higher than the current ub, no need to branch on it
		if(b.lb()>=upper_bound) {
			active_nodes.remove(b);
			return true;
		}
		return false;
	}
	
	public boolean check_integrity() {
		// retrieve current solution and objective
		List<Integer> sol = new ArrayList<Integer>();
		double cost = 0;
		try {
			for (Path path : paths) {
				if (this.masterproblem.cplex.getValue(path.y) > 0.99999) {
					// add selected routes
					sol.add(path.id);
					cost += path.cost;
				} else if(this.masterproblem.cplex.getValue(path.y) > 0.001) {
					// if not integer, return
					return false;
				}
			}
			// check if the feasible solution is better than the former one
			if(cost < this.upper_bound) {
				// if better, update incumbent_sol and upper bound
				this.incumbent_sol = sol;
				this.upper_bound = cost;
				return true;
			} else {return true;}
		} catch (IloException e) {
			System.err.println("Concert exception caught: " + e);
		}
		// return false by default
		return false;
	}
	
	public void branch(int strategy) {
		// branch on the total number of vehicles or on the number of crowd vehicles if possible
		double nb_vehicles = 0;
		double[] nb_crowd_vehicles = new double[Parameters.K-1];
		try {
			//nb_vehicles = masterproblem.cplex.getValue(masterproblem.total_vehicles_var);
			//System.out.println("there is "+nb_vehicles+" vehicles in total");
			nb_vehicles = masterproblem.cplex.getValue(masterproblem.number_vehicles_var.get(0));
			for(int k=1; k<Parameters.K;k++){
				//nb_crowd_vehicles[k-1] = masterproblem.cplex.getValue(masterproblem.total_crwvehicles_var.get(k-1));
				//System.out.println("there is "+nb_crowd_vehicles[k-1]+" vehicles of type "+k);
				nb_crowd_vehicles[k-1] = masterproblem.cplex.getValue(masterproblem.number_vehicles_var.get(k));
			}
		}catch (IloException e) {
			System.err.println("Concert exception caught: " + e);
		}
		if(nb_vehicles - Math.floor(nb_vehicles) > 0.01 && Math.ceil(nb_vehicles) - nb_vehicles > 0.01) {
			// if the number of vehicles is fractional
			//System.out.println("branching on total vehicle variable");
			new BBNode(current_bbNode,true, false,(int)Math.ceil(nb_vehicles), 0);
			new BBNode(current_bbNode,false,false,(int)Math.floor(nb_vehicles), 0);
		} else {
			boolean is_fractional=false;
			// or for the most fractional type out of the crowd vehicles type
			int most_fractional = 1;
			double most_fractional_value = 0.5;
			for(int k=1; k<Parameters.K;k++){
				if(nb_crowd_vehicles[k-1] - Math.floor(nb_crowd_vehicles[k-1]) > 0.01 && Math.ceil(nb_crowd_vehicles[k-1]) - nb_crowd_vehicles[k-1] > 0.01){
					double fractional_value = Math.abs(0.5-(nb_crowd_vehicles[k-1] - Math.floor(nb_crowd_vehicles[k-1])));
					if(fractional_value < most_fractional_value){
						most_fractional_value = fractional_value;
						most_fractional = k;
						is_fractional=true;
					}
				}
			}
			if(is_fractional){
				//System.out.println("branching on vehicle variable "+most_fractional);
				new BBNode(current_bbNode,true, true, (int)Math.ceil(nb_crowd_vehicles[most_fractional-1]), most_fractional);
				new BBNode(current_bbNode,false,true, (int)Math.floor(nb_crowd_vehicles[most_fractional-1]), most_fractional);

			} else{
				// otherwise, use the strategy passed to select an arc variable on which to branch
				//System.out.println("branching on arc variable");
				int var = selectvar(strategy);
				int i = first_index_arc(var);
				int j = second_index_arc(var);
				//System.out.println("branching on arc "+i+" "+j);
				new BBNode(i,j, true, current_bbNode); // variable >= 1
				new BBNode(i,j, false, current_bbNode); // variable = 0
			}
			
		}
	}
	
	private int selectvar(int strategy) {
		int var = 0;
		int nb_integer_vars = 0;
		int nb_fractional_vars = 0;
		int var_depot = 0;
		double depot_val = 0;
		int var_customer = 0;
		double cust_val = 0;
		//compute "arc variables values"
		double[][] arc_val = new double [all_nodes.size()][all_nodes.size()];
		try {
			for(Path p: paths){
				double path_val = masterproblem.cplex.getValue(p.y);
				if(path_val >0.0001){
					for(int i=0; i<all_nodes.size();i++){
						for(int j=0; j<all_nodes.size();j++){
							if(i!=j){
								arc_val[i][j] += (p.b(i,j)*path_val);
							}
						}
					}
				}
			}
		} catch (IloException e) {
			System.err.println("Concert exception caught: " + e);
		}
		// count the number of fractional and integer arc variables
		for(int i=0;i<all_nodes.size();i++){
			for(int j=0; j<all_nodes.size(); j++){
				if(j!=i){
					double val = arc_val[i][j];
					if( val > 0.00001 && val < 0.99999) {
						nb_fractional_vars += 1;
						if(i == source.id || j == sink.id) {
							if(strategy == 0) {
								// keep arc incident to the depot of most fractional value (strategy 0)
								if(Math.min(Math.ceil(val)-val,val) > depot_val) {
									depot_val = Math.min(Math.ceil(val)-val,val);
									var_depot = arc_index(i, j);
								}
							} else {
								// keep arc incident to the depot of highest fractional value (strategy !=0)
								if(val > depot_val) {
									depot_val = val;
									var_depot = arc_index(i, j);
								}
							}
						} else {
							// keep arc between customers of most fractional value
							if(strategy == 0) {
								if(Math.min(Math.ceil(val)-val,val)>cust_val) {
									cust_val = Math.min(Math.ceil(val)-val,val);
									var_customer = arc_index(i, j);
								}
							} else {
								// keep arc between customers of highest fractional value
								if(val > cust_val) {
									cust_val = val;
									var_customer = arc_index(i, j);
								}
							}
						}
					} else {
						nb_integer_vars += 1;
					}
				}
			}
		}
		if(nb_fractional_vars > 0) {
			current_bbNode.percent_int = (double)(nb_integer_vars)/(double)(nb_integer_vars + nb_fractional_vars);
		}
		if(var_depot > var_customer) {var = var_depot;}
		else {var = var_customer;}
		return var;
	}
	
	private int arc_index(int i, int j) {return i*(all_nodes.size()) + j;}
	private int first_index_arc(int i) {return i/(all_nodes.size());}
	private int second_index_arc(int i) {return i%(all_nodes.size());}
}
