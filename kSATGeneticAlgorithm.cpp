/*	
	==============================
	INTRO TO 3SAT DECISION PROBLEM
	==============================
	
	3SAT is a version of the Boolean satisfiability problem, aka SAT. The SAT problem is a decision problem which is concerned with answering whether or not a boolean expression is satisfiable, meaning there 
	is at least one set of truth assignments for which that expression evaluates to true. SAT requires expressions to be in a specific format called Conjunctive Normal Form, or CNF. Expressions in CNF are made up 
	of clauses, and these clauses are made up of literals. In SAT, clauses can be made up of any number of literals, but in 3SAT each clause must be 3 literals. Clauses do not require that their literals 
	be distinct- the same literal can be repeated three times to make a valid clause in 3SAT. Putting an example in front of us:

	(x1 v x2 v x3) ^ (!x1 v !x2 v !x3)

	Above is an expression that satisfies the format of 3SAT- it's in CNF, it has at most three literals per clause. In CNF, clauses are always of the form (literal or literal or literal). Clauses are always connected by an 
	'and', aka ^ above. v is the shorthand for or in this example. Expression in 3SAT can be much, much longer than this example- they can have any number of clauses connected via ^'s- but in 3SAT we can only 
	have at most three literals per clause. In regular SAT, we can have any number of literals per clause in addition to any number of clauses! That's too many variables to handle and creates a lot of computational 
	complexity. 3SAT is a more manageable reduction of SAT to handle computationally.

	So, in this example, is the expresion satisfiable? If x1 through x3 are all set to true, the second clause results in false. If x1 through x3 are all set to false, the first clause results in false. Both cases
	result in an overall false for the whole expression, as the expression requires that *each* clause be true. But if we pick x1 as true and the x2 and x3 as false (x2 is irrelevant as we only need one true in each clause), 
	we get a true for the first clause and a true for the second clause. A total of true for the expression. And so, this example expression is satisfiable. Job done. An example of an unsatisfiable 3SAT expression would be 
	the following:

	(x1 v x1 v x1) ^ (!x1 v !x1 v x1)

	No assignment of true or false to x1 will make both clauses true here. x1 = T means clause 2 is false. x1 = F means clause 1 is false. The expression is unsatisfiable, meaning it is always false. There is no truth value 
	assignment set that will make all the clauses in the expression true, and therefore the expression is unsatisfiable. 
	
	The task for this program is to create a set of satisfiable expressions of varying clause length. Only a certain percentage of expressions will need to be satisfiable for our purposes- it gets progressively harder to 
	create satisfiable expressions as the number of clauses grows greater. This certain percentage will be called our convergence ratio. Once iterations of expressions are showing around the same percentage of expressions 
	as satisfiable, we've converged the populations and are unlikely to get any greater gains in terms of satisfiability out of our population.

	========================
	GENETIC ALGORITHM PROPER
	========================

	How should we store a Bool expr in CNF? Could use a 2d array with n rows (representing clauses) and 3 columns (representing the literals in each clause) - but this is unnecessary.  We can instead use a bit string 
	made up of 3n total bits, each either 0 or 1 (false or true). We make a string of 3n total bits because every 3 bits in this string represents a clause- that 'clause' (position 0-2, 3-5, 6-8, etc in the bit string) 
	can be said to be false if its three bits are all 0. It will be said to be true if at least one of its bits is 1. n here represents the total number of clauses per expression. 3n represents the total number of literals 
	in that expression. Our total complexity will vary quite widely with n.

	Every population will contain some number of expressions that follow this specification. Each expression will be stored in a bitset with each index containing one literal, either 0 or 1. Each expression will have its 
	satisfiability recorded on a clause-level and an overall-expression-level. A population will hold a certain number of expressions, and within the population these expressions will be called chromosomes. A population will
	be said  to be fit if a certain percentage of its chromosomes are satisfiable, the convergence ratio alluded to in the former section. This particular percentage will be subject to change as it decides a great deal about 
	the total running time / resource use of the algorithm.

	Though my original intention with this project was to create a 3SAT Genetic Algorithm, I have modified the few things that were hardcoded for 3SAT and created a general purpose kSAT genetic algorithm that works for any k. 

*/

#include <iostream> // printing
#include <vector> // populations
#include <bitset> // chromosomes
#include <deque> // convergence
#include <random> // random generation of bitsets, % chances of selection/crossover/mutation
#include <algorithm> // find()

using namespace std;

// the variables controlling the size of our populations and their chromosomes. Modify these!

// chromosome control
int number_of_clauses = 500; // our n, the principal variable of our algorithm
int clause_length = 3; // Our kSAT modifier. Modify this to create 4SAT, 5SAT, etc instances. 
int expression_length = clause_length * number_of_clauses; // aka the length of the boolean expression for a given chromosome. **IF YOU MODIFY THE ABOVE TWO VARIABLES TO CHANGE THIS, EXPRESSION BITSET IN THE CHROMOSOME STRUCT MUST MATCH EXPRESSION_LENGTH'S VALUE!**

// population control 
int population_size = 500; // each population holds this many chromosomes

// variables controlling genetic alg operations
double selection_rate = 1.0; // % of chromosomes being passed to tournament. 
double tournament_selection_rate = 0.65; // % of selected chromosomes who are going to move on to next generation by winning tournament in tournamentSelection, see tournamentSelection(). 
double crossover_rate = 0.40; // % chance replacing two parent chromosomes with their kids.
int total_crossover_exchanges = (int) number_of_clauses * 0.25; // determines number of clauses to exchange in crossover.
double mutation_rate = 0.025; // % chance a literal in a chromosome has its value flipped.
double convergence_threshold = 0.02; // if fitness differentials between past pops and current pop are at most conv_thresh apart, converge. total fitness is determined by percent of satisfiable clauses in each chrome of a population.
int fitness_memory_size = 10; // used for convergence, the number of populations whose fitnesses we're going to keep in mind when determining if pops are conv_thresh% similar in total fitness.

// bitset size must be known at compile time- cannot set each a bitset's size to a variable. thus our size below must be constant, so expression's size will always have to be fixed to be in line with expression_length above.
struct chromosome {
	bitset<1500> expression; // aka an individual 3SAT boolean expression in CNF
	double percentage_satisfiable_clauses = 0.0; // percentage of clauses that are satisfiable in expression, useful for determining chromosomes whose expression aren't entirely satisfiable
};

typedef vector<chromosome> population; // the population containing our chromosomes. its size isn't determined here, but it will be filled with population_size chromosomes in population generation related functions.

void generateInitPop(population& initPop) {

	random_device rd; // obtain a random number from hardware
	mt19937 eng(rd()); // seed the generator
	uniform_int_distribution<> dis(0, 1); // if the random generator flips rolls a 0, set bit to 0. if it rolls a 1, set bit to 1.

	while (initPop.size() != population_size) {
		chromosome c0;
		for (int i = 0; i < expression_length; i++) { // setting initial values of each bit in expression.
			c0.expression[i] = dis(eng); // will roll either 0 or 1.
		}
		initPop.push_back(c0);
	}
}

// sorts populations so that the highest fitness chromosomes come to the front of the population.
bool topDownFitnessSort(chromosome x, chromosome y) {
	return (x.percentage_satisfiable_clauses > y.percentage_satisfiable_clauses);
}

void sortByFitness(population& pop) {
	sort(pop.begin(), pop.end(), topDownFitnessSort);
}

void fitnessFunction(population& pop) {
	
	bool satisfiable_clause = 0;
	double sum_of_population_fitness = 0;
	for (int i = 0; i < population_size; i++) { // iterate through all chromos in population
		int num_clauses_satisfiable = 0; // per chromosome number of clauses that are satisfiable

		for (int j = 0; j < expression_length; j++) { 

			if (pop[i].expression[j] == 1) { // evaluating at a clause by clause level rather than a literal by literal level- if there's at least one true (1) in the length of a clause, the clause is satisfiable
				satisfiable_clause = 1;
			}

			if ((j + 1) % clause_length == 0) { // must perform j + 1 here because the bitset counts from 0; 
												// in case where clause length = 3: 0-2 is a clause, 3-5 is a clause, etc. if during the movement through a clause at least one of the literal spots in that clause is true, increase num_clauses_sat.
				if (satisfiable_clause) {
					num_clauses_satisfiable++;
				}
				satisfiable_clause = 0; // return satisfiable_clause to false for next clause.
			}
		}

		pop[i].percentage_satisfiable_clauses = (double) num_clauses_satisfiable / number_of_clauses; // percentage of clauses that are satisfiable
	}

	sortByFitness(pop); // sort pop from best to worst top down as our final task for fitfunct..
}

/* Selection: chromosomes with higher percentage_satisfiable_clauses are selected to move into the next population. Chromes w/ perentage_satisfiable_clauses of 1 are *extremely* high value members of the population, as the goal is 
   having convergence_ratio % of chromosomes having a expression_satisfiable_overall of 1 across multiple populations in sequence. For selection purposes, we will use Tournament Selection as defined in class notes, where algorithm
   will select chromosomes randomly until it reaches the selection_rate # of chromsomes selected. All populations passed to this function *must* have gone through the fitness function first to initialize their fitness related fields.
   
   In class, tournamentSelection was defined as "select n indidivuals from the population and then select the m most fit indidividuals from that n amount of indviduals for selection into next generation." For this program, 
   our n in this scenario is selection_rate while our m is tournament_selection_rate. Our *actual* number of chromosomes selected is (selection_rate * tournament_selection_rate) pop_size.
*/ 

population tournamentSelection(population& pop) {

	random_device rd; // obtain a random number from hardware
	mt19937 eng(rd()); // seed the generator
	uniform_int_distribution<> dis(0, population_size - 1); // roll a random int from 0 to population size. select that index to move on to be judged in a tournament decided by fitness. chromosomes that win the tournament move on to the next gen.
	int total_indices_to_select = (int) population_size * selection_rate; // select selection_rate many indices from the population. 
	vector<int> randomly_selected_indices; // recording which indices we'll select from the populaton passed to tournamentSelection.

	while (randomly_selected_indices.size() < total_indices_to_select) {
		int i = dis(eng);
		while (find(randomly_selected_indices.begin(), randomly_selected_indices.end(), i) != randomly_selected_indices.end()) { // no repeated indices
			i = dis(eng);
		}
		randomly_selected_indices.push_back(i);
	}

	population selected_chromosomes; // filled with chromosomes from the population passed as argument to this function whose indices are present in randomly_selected_indices.
	for (int i = 0; i < population_size; i++) {
		if (find(randomly_selected_indices.begin(), randomly_selected_indices.end(), i) != randomly_selected_indices.end()) {
			selected_chromosomes.push_back(pop[i]);
		}
	}

	sortByFitness(selected_chromosomes); // sort the selected_chromosomes by fitness 
	int tournament_selection = (int) total_indices_to_select * tournament_selection_rate; // percentage of selected_chromosomes who are going to actually make it to the next generation. 
	population tournament_winners; 

	for (int i = 0; i < tournament_selection; i++) {
		tournament_winners.push_back(pop[i]);
	}

	return tournament_winners;
}

/* Crossover: chromosomes that were selected from tournamentSelection have crossover_rate chance to mate and replace themselves with their children. Mating in this problem involves parent chromosomes exchanging clause_length # of bits *at any point in the expr*
   with the other parent. The number of bits being exchanged being the same as clause_length allows for a situation in which parent1 exchanges the last bit of one clause for the first two bits of another clause with parent2, and this exchange
   mutually makes both clauses in the expression satisfiable. Through this exchange of clause_length bits, the hope is that children will have a higher percentage_satisfiable_clauses than either of their parents. The chance that exchanges will be neutral
   or positive rather than negative will rise as the percentage_satisfiable_clauses number for parents rises.

   The *number* of clauses being exchanged is dictated in the global variable section. 
*/

population crossover(chromosome parent1, chromosome parent2) {
	
	random_device rd; // obtain a random number from hardware
	mt19937 eng(rd()); // seed the generator
	uniform_int_distribution<> dis(0, expression_length - clause_length); // covers beginning of expression to the last possible clause_length # of bits in expression.

	/* When selecting the bitset indices here, we want to make sure that the total_crossover_exchanges number of triples that we generate are all *distinct*, meaning that each triple doesn't overlap with any other triple already selected.
	   Example: if we select our first triple as 0 through 2, we do *not* want another triple to be 2 through 4. The next available sequential triple in the bitset should be 3 through 5 in the case that 0 through 2 has already 
	   been selected. So we are cautious of this situation below.
	*/
	vector<int> selected_bits; // will contain the start points of the clause_lengths we wish to exchange.

	while (selected_bits.size() < total_crossover_exchanges) {
		int i = dis(eng); 
		while (find(selected_bits.begin(), selected_bits.end(), i) != selected_bits.end()) { // our check to guarantee that we found the start of a clause as well as if that clause start is already in selected_bits
			i = dis(eng);
		}
		selected_bits.push_back(i); // push back the bits that we'll be exchanging between parents.
	}
	// now need to grab these clause_lengths in both parents and exchange them.
	vector<int> parent1_container (clause_length); // containers for any triple in parent1 or parent2. 
	vector<int> parent2_container (clause_length);

	int i = 0;
	while (i < expression_length) {
		if (find(selected_bits.begin(), selected_bits.end(), i) != selected_bits.end()) { // if our current i is in selected_bits, it's a start point for our triple!
			// put our clause_lengths in our parent1 and 2 containers. swap them in the same step.
			for (int j = 0; j < clause_length; j++) {
				parent1_container[j] = parent1.expression[i + j];
				parent2_container[j] = parent2.expression[i + j];
				parent1.expression[i + j] = parent2_container[j];
				parent2.expression[i + j] = parent1_container[j];
			}
			i += clause_length;
		} else {
			i++;
		}
	}
	// after this completes there's no more swapping that needs to be done! the parents are exchanged! we can return them both now, renamed as their children!
	population child_container;
	chromosome child1 = parent1; // note that the fitness of these two children has *surely* changed. we will have to use the fitness function again to get the correct valuation, but this will be done later.
	chromosome child2 = parent2;
	child_container.push_back(child1);
	child_container.push_back(child2);

	return child_container;
}

// Mutate: If a chromosome is selected for mutation (mutation_rate % chance) it gets sent here and gets a random bit flipped. Pretty straightforward.

void mutate(chromosome c0) {
	random_device rd; // obtain a random number from hardware
	mt19937 eng(rd()); // seed the generator
	uniform_int_distribution<> dis(0, expression_length - 1); 

	int i = dis(eng);
	c0.expression[i].flip();
}

/* A necessary function for generateNextPop- cannot just drop the random chromosome generator into genNextPop as it absolutely requires use of random_device, and it's illegal to initialize random_device more than once per function. Hence, we need this repeat
   of generateInitPop in front of generateNextPop in order to generate remaining chromosomes that might be absent fron generateNextPop.
*/

void generateChromosomes(population& pop, int number_to_generate) {
	random_device rd; // obtain a random number from hardware
	mt19937 eng(rd()); // seed the generator
	uniform_int_distribution<> dis(0, 1); // 0 bit or 1 bit as in generateInitPop
	int number_genned = 0;

	while (number_genned < number_to_generate) { // create random chromosomes.
		chromosome c0;
		for (int i = 0; i < expression_length; i++) { // setting initial values of each bit in expression.
			c0.expression[i] = dis(eng); // will roll either 0 or 1.
		}
		pop.push_back(c0);
		number_genned++;
	}
}

// Task of this function is to generate all populations following the initial population. This function calls selection, crossover and mutation functions and ultimately returns a new population with population_size chromosomes.

population generateNextPop(population& pop) { 
	
	population next_population; // the population we'll return. where we'll be depositing selected, crossovered, and mutated chromosomes from the population passed as argument.
	population tournament_winners = tournamentSelection(pop); // perform the selection process for the current population straight away. 

	random_device rd; // obtain a random number from hardware
	mt19937 eng(rd()); // seed the generator
	uniform_real_distribution<> dis(0.0, 1.0); // used for crossover chance
	population children(2); 

	for (int i = 0; i < tournament_winners.size() - 1; i += 2 ) { // jump by 2 per iteration of for loop because we want to grab the i'th member of tournament_winners as well as the i'th + 1 member, its fellow parent. stop at size() - 1 so that we don't 
																  // exceed the bounds of whatever tournament_winners size is, and allows the parent1 = winners[n-1] & parent2 = winners[n] combination.
		if (crossover_rate == 0.0 || population_size < 2) {
			break; // crossover disabled for this GA run if crossover_rate equals 0.0 or if there aren't 2 chromosomes to mate.
		}
		if (dis(eng) <= crossover_rate) {
			children.clear();
			children = crossover(tournament_winners[i], tournament_winners[i + 1]); // generate kids
			tournament_winners[i] = children[0]; // replace parents with kids
			tournament_winners[i + 1] = children[1];
		}
	}

	for (int i = 0; i < tournament_winners.size() - 1; i++) {
		next_population.push_back(tournament_winners[i]); // fill the next_population with the tournament winners and those winners who turned into their kids. absolutely will not fill next_pop to be population_size- generate the remainder as random chromosomes.
	} 

	generateChromosomes(next_population, population_size - next_population.size()); // chromes generated by this function will not have their fitnesses determined.

	for (int i = 0; i < population_size; i++) { // one last thing- run mutation chance on all of the chromes in next_pop.
		if (dis(eng) < mutation_rate) {
			mutate(next_population[i]);
		}
	}

	fitnessFunction(next_population); // redetermine fitnesses after mutation is complete.

	// next_population's creation is now complete. fully sized with some selected, mutated, and random chromosomes
	return next_population;
}

int main() {

	cout << "Parameters for this run of the GA:	" << endl;
	cout <<	"Expr length: " << expression_length << "     Clause length: " << clause_length << "     Pop size: " << population_size << "     Selection rate: " << selection_rate * tournament_selection_rate << "     Crossover rate: " << crossover_rate << endl;
	population init_pop; // create the initial pop
	generateInitPop(init_pop);
	population current_pop = init_pop; // set the init_pop to be the current_pop we're analyzing- this population will change as we iterate through generations.
	fitnessFunction(current_pop); // get the fitness values for all chromes squared away, sort the pop by fitness.
	double total_fitness_of_population = 0.0;

	for (int i = 0; i < population_size; i++) {
		total_fitness_of_population += current_pop[i].percentage_satisfiable_clauses; // get total fitness of the current_pop. higher number is better- higher means that there is a greater # of clauses satisfiable across all chromes.
	}

	deque<double> fitness_memory; // will record the fitnesses of past populations and compare them to determine if the GA has converged or not. deques are FIFO, useful for this recording of x last populations.
	deque<double> fitness_differentials; // those comparisons will be held inside a different deque called fitness_differentials- if the difference between any two total_fitnesses of a population is sufficiently small across some # of populations, GA has converged
	fitness_memory.push_back(total_fitness_of_population); // pushes back current_pop's total fitness.
	int fitness_counter = 0; // used to determine which index of fitness_differentials we're at. we only want to keep the past fitnesses/diffs of just a small portion of the number of populations that will be generated.

	int population_iteration = 1;
	
	double average_satisfiable_clauses = total_fitness_of_population / number_of_clauses;

	cout << "Population # " << population_iteration << "				Average satisfiable clauses across whole population: " << average_satisfiable_clauses * 100 << endl;
	cout << "The most fit chromosome in the initial pop's percentage of satisfiable clauses is " << current_pop[0].percentage_satisfiable_clauses << endl;

	population next_pop;

	while (1) { // run until convergence.
		total_fitness_of_population = 0.0; // reset total fitness for new gen.
		next_pop = generateNextPop(current_pop);
		current_pop = next_pop;

		for (int i = 0; i < population_size; i++) {
			total_fitness_of_population += current_pop[i].percentage_satisfiable_clauses; // get total fitness of the current_pop. higher number is better- higher means that there is a greater # of clauses satisfiable across all chromes.
		}

		double sum = 0.0;
		double average_satisfiable_clauses = total_fitness_of_population / number_of_clauses;

		// fitness logging and differentials section
		if (fitness_memory.size() == fitness_memory_size) { // if our fitness memory is reaching the size limit....
			fitness_memory.pop_front(); // remove first emplaced entry. 
			fitness_memory.push_back(total_fitness_of_population); // place the new entry in.
		} else {
			fitness_memory.push_back(total_fitness_of_population);
		}

		/* If the number of populations whose fitnesses we're keeping in memory is equal to 5, then the number of differentials between these 5 populations is equal to 4- that is, the set of fitness diffs (2-1) (3-2) (4-3) (5-4) in the case of 5 total populations
		   kept in the memory container. When we reach this scenario of (2-1) (3-2) (4-3) (5-4), we want the first differential emplaced in fitness_diffs (aka (2-1)) to go and to bring in (6-5), such that the result is (3-2) (4-3) (5-4) (6-5). We know to start 
		   pop_fronting once fitness_memory.size() is equivalent to the size set in the global variables, because if fitness_memory has hit its size constraint, so too has fitness_differentials.
		   
		*/

		double diff = 0.0;
		int fitness_diff_size = (fitness_memory_size - 1);

		if (fitness_memory.size() == fitness_memory_size) { // once fitness memory is full, always do this. this section could honestly go in the if above the comment block.
			diff = fitness_memory[fitness_memory_size - 1] - fitness_memory[fitness_memory_size - 2];
			diff = abs(diff);
			fitness_differentials.pop_front();
			fitness_differentials.push_back(diff);
		} else { // do this until fitness_memory is full. if fitness_memory is full, then fitness_differentials is also full.
			diff = fitness_memory[population_iteration] - fitness_memory[population_iteration - 1];
			diff = abs(diff);
			fitness_differentials.push_back(diff); 
		}
		population_iteration++;

		//convergence checking section
		for (int i = 0; i < fitness_diff_size; i++) {
			if (fitness_differentials[i] > convergence_threshold) { // do the past fitness_memory_size populations all fall under a certain bound in regards to overall fitness?
				break; // if not, get outta here and continue the generating of new populations.
			}
			cout << "Convegence reached! Population number: " << population_iteration << endl;
			cout << "Most fit chromosome in this population has the following expression: " << endl;
			for (int j = 0; j < expression_length; j++) {
				if ((j + 1) % clause_length == 0) { // if we're at a clause point
					cout << current_pop[0].expression[j] << " | "; // have | as a delimiter
				}
				else { // general case, midclause point or at index 0 of expression
					cout << current_pop[0].expression[j];
				}
			}
			cout << endl;
			cout << "The most fit chromosome in the final pop's percentage of satisfiable clauses is " << current_pop[0].percentage_satisfiable_clauses << endl;

			cout << "Average satisfiable clauses for final population is " << average_satisfiable_clauses << endl;
			// convergence reached, print resulting population/best fitness chromosome, end program.
			return 0;
		}

		cout << "Population # " << population_iteration << "				Average satisfiable clauses across whole population: " << average_satisfiable_clauses * 100 << endl;
	}

	/*	
		===================================================
		AN IMPORTANT NOTE ON PERCENTAGE_SATISFIABLE_CLAUSES
		===================================================

		Depending on which k you use for kSAT, the random generator that makes the initial population is going to have a different result for what the percentage_satisfiable_clauses value starts out at. A clause is satisfiable if it has *at least* one true 
		in its clause_length number of bits. A clause is unsatisfiable if it only contains falses. The percent chance we obtain all falses for a clause of length 3 is equal to 0.5 * 0.5 * 0.5 = 0.125. In other words, the number of unsatisfiable clauses in 
		a 3SAT instance will only be 12.5%. And so, the percentage_satisfiable_clauses value output by the algorithm in a 3SAT instance will always be around 87.5%. For 4SAT, a population will have 6.25% unsatisfiable clauses and 93.75% satisfiable clauses to start. 
		For 5SAT, it's 3.125% unsat, 96.875% sat. And so on. The algorithm will increase this satisfiability percentage as much as it can, but the starting point of percentage_sat_clauses will always be dictated by dependent probability in this way.

	*/
}


