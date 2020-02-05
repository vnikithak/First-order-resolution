# First-order-resolution
Implements first order resolution between CNF sentences

Format for input.txt:

<N = NUMBER OF QUERIES>
<QUERY 1>
...
<QUERY N>
<K = NUMBER OF GIVEN SENTENCES IN THE KNOWLEDGE BASE>
<SENTENCE 1>
...
<SENTENCE K>
  
The first line contains an integer N specifying the number of queries. The following N lines contain one query per line. The line after the last query contains an integer K specifying the number of sentences in the knowledge base. The remaining K lines contain the sentences in the knowledge base, one sentence per line. 

Query format:

Each query will be a single literal of the form Predicate(Constant_Arguments)or ~Predicate(Constant_Arguments)and will not contain any variables.Each predicate will have between 1 and 25 constant arguments. Two or more arguments will be separated by comma.

KB format:Each sentence in the knowledge base is written in one of the following forms:1)An implicationof the form p1∧p2∧... ∧pm⇒q, where its premise is a conjunction of literals and its conclusion is a single literal.Remember that a literal is an atomic sentence or a negated atomic sentence.2)A single literal: qor ~q

The output is printed in the following format in output.txt:

For each query, it is determined if that query can be inferred from the knowledge base or not, one query per line:
<ANSWER 1>
...
<ANSWER N>
  
  
To run the fol.py:

 python fol.py
