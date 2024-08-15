public final class Probability {
	public static double cumulative_bi(int n, int k, double p) {
		double cumul = 0.0;
		if (n < k || p > 1 || p < 0) { System.out.println("Probability Error n must be larger than k and p must be 1 > p > 0 ");
			return cumul; }
		else if (n == k) { cumul = 1 - Math.pow(p, n); return cumul; }
		else if (k == 0) { return cumul; }
		else {
			for (int i = 0; i < k; i++) {
				double p_1 = Math.pow(p, i);
				double p_2 = Math.pow(1 - p, n - i);
				double produ = 1;
				int n_k = n - i;
				if (n_k <= n / 2) {
					for (int j = 1; j <= n_k; j++) {
						produ *= (double)(n - n_k + j)*(1 - p) / (double)j;
					}
					cumul += produ * p_1;
				}
				else {
					for (int j = 1; j <= i; j++) {
						produ *= (double)(n - i + j)*p / (double)j;
						
					}
					cumul += produ * p_2;
				}
			}
			return cumul;
		}
	}
}
