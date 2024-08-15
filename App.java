public class App {
	public static void main(String[] args) {
		String instance = "A-n32-k5.vrp";
		
		// initialize the problem and bbnodes list and parameters
		BranchPriceCut bpc = new BranchPriceCut(instance);
		System.out.println("solving instance " + instance + " with " + Parameters.num_customers+" customers");
		
		// start solving
		int iter = 0;
		double time_limit = 3600;
		while((bpc.logger.timeStamp()<time_limit) && bpc.active_nodes.size()>0) {
			// choose next bbnode : 0 is best bound first and 1 is most integer
			int next_bbnode_strategy = 0;
			if(iter%100 == 0) {next_bbnode_strategy=1;}else {next_bbnode_strategy=0;}
			bpc.select_BBNode(next_bbnode_strategy);
			// run column generation (and cuts) on the bbnode
			bpc.runColumnGeneration();
			// check for pruning (feasibility/upperbound)
			if(bpc.prune_bbnode(bpc.current_bbNode)) {
				//System.out.println("a node has been pruned");
				iter++;
			// check integrity of the solution
			} else if(bpc.check_integrity()) {
				System.out.println("found feasible solution");
				bpc.masterproblem.displaySolution(false);
				bpc.active_nodes.remove(bpc.current_bbNode);
				iter++;
			// otherwise, branch
			} else {
				System.out.println("Time " + Math.ceil(bpc.logger.timeStamp()) + " Lower bound = " + bpc.lower_bound + " Upper bound = " +bpc.upper_bound);
				System.out.println("GAP = " + (100*(bpc.upper_bound-bpc.lower_bound)/bpc.lower_bound) + "%");
				bpc.branch(0);// strategy 0 most fractional
				bpc.active_nodes.remove(bpc.current_bbNode);
				iter++;
			}
			if(bpc.logger.timeStamp()>=time_limit){System.out.println("time limit exceeded :'-(");}
		}
	}
}
