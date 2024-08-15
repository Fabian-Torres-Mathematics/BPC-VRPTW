import ilog.concert.*;
import ilog.cplex.*;


public final class Parameters {
	public static int K; // number of categories including PDs
	public static int num_customers;
	public static int[] Q;
	public static int[] F;
	public static double penalty = 2.0;
	public static double[] V;
	private static int[] pool_sizes;
	public static int[] max_pref;
	private static double[] proba_bi;
	private static double[] ratio;
	public static double [][] fixed_cost;
	public static double [][] variable_cost;
	public static double [][] recourse_prob;
	public static int delta_ng = 8;
	
	public static void param(int k, int q, int num) {
		K = k;
		num_customers = num;
		Q = new int[K];
		Q[0]=q;
		for(int i=1; i<K;i++) {
			Q[i] = q-2*i*q/10;
		}
		F = new int[K];
		for(int i=0; i<K; i++) {
			F[i]=Q[i]/2;
		}
		System.out.println("professional vehicle has capacity "+Q[0]+" and price "+F[0]);
		V = new double[K];
		V[0]=2.0;
		pool_sizes = new int[K];
		pool_sizes[0]=0;
		max_pref = new int[K];
		max_pref[0]=0;
		proba_bi = new double[K];
		proba_bi[0]=1.0;
		for(int i=1; i<K; i++) {
			V[i]=1.0;
			pool_sizes[i] = 2*i*num_customers;
			max_pref[i]= 2*i*num_customers;
			proba_bi[i]=0.05;
		}
		Cal_max_pref();
	}
	
	private static void Cal_max_pref() {
		// categories for CDs are denoted 1,...,K-1
		fixed_cost = new double[K][];
		variable_cost = new double[K][];
		recourse_prob = new double[K][];
		fixed_cost[0] = new double[1];
		fixed_cost[0][0] = F[0];
		variable_cost[0] = new double[1];
		variable_cost[0][0] = V[0];
		recourse_prob[0] = new double[1];
		recourse_prob[0][0] = 0;
		ratio = new double[K];
		ratio[0]=0;
		
		for(int k=1; k<K; k++) {
			double a = (penalty*V[0] - V[0])/(penalty*V[0] - V[k]);
			double b = (penalty*F[0] - F[0])/(penalty*F[0] - F[k]);
			if(a<0) {a = 1;}
			if(b<0) {b = 1;}
			ratio[k] = Math.min(a,b);
		}

		for(int k=1; k<K; k++){
			recourse_prob[k] = new double[pool_sizes[k]+1];
			for(int s=1; s<=pool_sizes[k]; s++) {
				double p = Probability.cumulative_bi(pool_sizes[k], s, proba_bi[k]); //probability of failure
				if((1-p) < ratio[k]){max_pref[k] = s - 1;break;
				} else {
					recourse_prob[k][s] = p;
				}
			}
			System.out.println("vehicle type "+k+" with capacity "+Q[k]+" has max preference "+max_pref[k]+" and price "+F[k]);
		}

		for(int k=1; k<K; k++){
			fixed_cost[k] = new double[max_pref[k] + 1];
			variable_cost[k] = new double[max_pref[k] + 1];
			recourse_prob[k] = new double [max_pref[k] + 1];
			fixed_cost[k][0] = Double.POSITIVE_INFINITY;
			variable_cost[k][0] = Double.POSITIVE_INFINITY;
			recourse_prob[k][0] = Double.POSITIVE_INFINITY;
			for(int s=1; s<=max_pref[k];s++){
				fixed_cost[k][s] = F[k]*(1.0 - recourse_prob[k][s]) + penalty*F[0]*recourse_prob[k][s];
				variable_cost[k][s] = V[k]*(1.0 - recourse_prob[k][s]) + penalty*V[0]*recourse_prob[k][s];
			}
		}
	}
	
	public static void configureCplex(BranchPriceCut.MasterProblem masterproblem) {
		try {
			// branch and bound
			masterproblem.cplex.setParam(IloCplex.Param.MIP.Strategy.NodeSelect, 1);
			masterproblem.cplex.setParam(IloCplex.Param.MIP.Strategy.Branch,1);
			//masterproblem.cplex.setParam(IloCplex.Param.Preprocessing.Presolve, true);
			// display options
			masterproblem.cplex.setParam(IloCplex.Param.MIP.Display, 2);
			masterproblem.cplex.setParam(IloCplex.Param.Tune.Display, 1);
			masterproblem.cplex.setParam(IloCplex.Param.Simplex.Display, 0);
		}
		catch (IloException e) {System.err.println("Concert exception caught: " + e);}
	}
}
