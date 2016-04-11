// Kevin Yen Jan 24
#include "scanner.h"
#include <sstream>
#include <fstream>
#include <vector>

using namespace std;

struct node{ //
	int index; // current index
	string key; // content of the node
	int back; // back link to it's father/mother/whoever-adpoted-this-node.
	int left; // index number of left child
	int right; // index number of right child
};

struct TreeNode{
  string key;
  struct TreeNode *left;
  struct TreeNode *right;
  string type;
  bool couldbeNIL;
};

struct TreeNode *root =0;
Scanner s;
stringstream ss;
vector<node> tree,tree2;
int focus,treeindex;

ofstream myfile;

void debug(){
	cout<<"QWERQWRE"<<endl;
	exit(0);
}

// functions for c++98
int to_int(string in){
	int out;
	istringstream(in) >> out;
	return out;
} 

string to_str(int in){
	string s;
	stringstream out;
	out << in;
	s = out.str();
	return s;
}

inline bool is_number(const std::string & s)
{
   if(s.empty() || ((!isdigit(s[0])) && (s[0] != '-') && (s[0] != '+'))) return false ;

   char * p ;
   strtol(s.c_str(), &p, 10) ;

   return (*p == 0) ;
}

// returns a node, for constructing the vector.
node anode(int index, string key, int back, int left, int right){
	node temp;
	temp.back = back;
	temp.index = index;
	temp.key = key;
	temp.left = left;
	temp.right = right;
	return temp;
}

// initialize tree for new Expr
void treeinit(){
	tree.clear();
	focus = 0;
	treeindex = 0;
	tree.push_back(anode(0,"",-1,-1,-1));
}

void newnode(){
	tree[focus].left = ++treeindex;
	tree.push_back(anode(treeindex,"",focus,-1,-1));
	tree[focus].right = ++treeindex;
	tree.push_back(anode(treeindex,"",focus,-1,-1));
	focus = tree[focus].left;
}

void focusright(){focus = tree[tree[focus].back].right;}

void fillnode(string key){tree[focus].key = key;}

void focusback(){focus = tree[focus].back;}



// main stuff. Start(), Expr(), and List().
void Expr();
void List();

// Check() checks for any error messages to show. If error appears, print error and exit the whole program.
void Check(){
	if(s.Current.Type=="ERROR" || !s.error.empty()){
		// returning token is ERROR or the string named error is written by something.
		cout << "ERROR: " << s.error << endl;
		exit(0);
	}else if (s.Current.Type=="EOF"){
		// this happens when file ended but the grammar is not finished.
		cout << "ERROR: [syntax error] sentence not finished?" << endl;;
		exit(0);
	}
}

void drawtreeDOT(int index){
	// not exist
	if(index == -1) return;
	// alone, not a list
	if(tree[index].left==-1 && tree[index].right==-1){
		myfile << "\t" <<  tree[index].key << tree[index].index;
		myfile << ";" << endl;
		return;
	}
	myfile << "\t" <<  tree[index].key << tree[index].index << " -> " << tree[tree[index].left].key << tree[tree[index].left].index << ";" << endl;
	myfile << "\t" <<  tree[index].key << tree[index].index << " -> " << tree[tree[index].right].key << tree[tree[index].right].index << ";" << endl;
	drawtreeDOT(tree[index].left);
	drawtreeDOT(tree[index].right);
}

struct TreeNode* NewNode(string data) { 
  struct TreeNode* leaf = new(struct TreeNode);    // "new" is like "malloc" 
  leaf->key = data; 
  leaf->left = NULL; 
  leaf->right = NULL;

  return(leaf); 
} 

struct TreeNode* insert(struct TreeNode* leaf, string data) { 
  // 1. If the tree is empty, return a new, single node 
  if (leaf == NULL) { 
    return(NewNode(data)); 
  } 
  else { 
    // 2. Otherwise, recur down the tree 
    if (data <= leaf->key) leaf->left = insert(leaf->left, data); 
    else leaf->right = insert(leaf->right, data);

    return(leaf); // return the (unchanged) node pointer 
  } 
} 

void printTree(struct TreeNode* node) { 
  if (node == NULL) return;
  printTree(node->left); 
  cout << node->key; 
  printTree(node->right); 
} 

bool isLetter(struct TreeNode **leaf){
	if((*leaf)->key[0]>=65 && (*leaf)->key[0]<=90) return true;
	return false;
}

bool is_atom(struct TreeNode *leaf){
	if(leaf->left == NULL)
		return true;
	return false;
}

bool is_list(struct TreeNode *leaf){
	if(leaf->right==NULL){
		if(leaf->key!="NIL")return false;
		else return true;
	}else return is_list(leaf->right);
}

bool si_list(struct TreeNode *leaf){
	if(!is_list(leaf->left)) return false;
	if(leaf->right->key=="NIL") return true;
	return si_list(leaf->right);
}

int treelength(struct TreeNode *leaf){
	if(!is_list(leaf)){
		cout << "ERROR : length undefined, input is not a list" << endl;
		exit(0);
	}
	if(leaf->key == "NIL") return 0;
	return 1 + treelength(leaf->right);
}

bool si_length(struct TreeNode *leaf){
	if(treelength(leaf->left)!=2) return false;
	if(leaf->right->key=="NIL") return true;
	return si_length(leaf->right);
}

struct TreeNode* eval(struct TreeNode* leaf);

struct TreeNode* cond(struct TreeNode* leaf, string type){
	if(leaf->key=="NIL"){
			cout << "ERROR : undefined COND, no default T case. " <<endl;
			exit(0);
	}
	if (eval(leaf->left->right->left)->type!=type)
	{
		cout << "ERROR : [Type]COND's type should all be the same. " <<endl;
		exit(0);
	}
	if(eval(leaf->left->left)->key=="T") return eval(leaf->left->right->left); // good
	else if(eval(leaf->left->left)->key=="F") return cond(leaf->right, type);
	cout << "ERROR : [Type]undefined COND " <<endl;
	exit(0);
}

bool NILcheck(struct TreeNode* leaf){
	if(leaf->key=="NIL") return false;
	if(eval(leaf->left->right->left)->type=="List"&&eval(leaf->left->right->left)->key=="NIL")
		return true;
	else
		return NILcheck(leaf->right);
}

bool numberCheck(struct TreeNode* leaf){
	if(leaf->key=="NIL")
		return true;
	if(is_number(leaf->left->key))
		return numberCheck(leaf->right);
	else
		return false;
}

bool is_listofnumbers(struct TreeNode* leaf){
	if(is_list(leaf)&&numberCheck(leaf)){
		return true;
	}
	return false;
}

// Eval implementation
struct TreeNode* eval(struct TreeNode* leaf){
	//not a s-expression

// ******* RULE LEVEL 1 ********
// *******     ATOM     ********
// ******* RULE LEVEL 1 ********
	if(!leaf->key.empty()){
		if((is_number(leaf->key)))// number
		{
			struct TreeNode *temp = NewNode(leaf->key);
			temp->type = "Nat";
			return temp;
		}
		if ((leaf->key=="T")||(leaf->key=="F")) // T, F
		{
			struct TreeNode *temp = NewNode(leaf->key);
			temp->type = "Bool";
			return temp;
		}
		if ((leaf->key=="NIL")) // NIL
		{
			struct TreeNode *temp = NewNode(leaf->key);
			temp->type = "List";
			return temp;
		}
		cout << "ERROR : undefined atom " << leaf->key <<endl;
		exit(0);
	}
// ******* RULE LEVEL 1.5 ********
// *******     List of numbers     ********
// ******* RULE LEVEL 1.5 ********
	// if(is_listofnumbers(leaf)){
	// 	return leaf;
	// }
// ******* RULE LEVEL 2 ********
// ******* RULE LEVEL 2 ********
// ******* RULE LEVEL 2 ********
	//CAR
	if(leaf->left->key=="CAR"){
		if (treelength(leaf)!=2)
		{
			cout << "ERROR : CAR undefined (treelength(leaf)!=2)" << endl;
			exit(0);
		}
		struct TreeNode *temp = 0;
		temp = eval(leaf->right->left); // temp is input of CAR
		// if(temp->key=="NIL"){
		// 	cout << "ERROR : CAR input can't be a list that is empty" << endl;
		// 	exit(0);
		// }
		///////////// TYPE/////////////
		if (temp->type=="List"&&temp->key=="NIL")
		{
			cout << "ERROR : [Type]CAR input can't be a list that is empty" << endl;
			exit(0);
		}
		if (temp->type!="List")
		{
			cout << "ERROR : [Type]CAR input should be list of numbers" << endl;
			exit(0);
		}
		if (temp->couldbeNIL==true)
		{
			cout << "ERROR : [Type]CAR Static checking found potentially-empty lists" << endl;
			exit(0);
		}
		//////////////////////////////////
		if(is_atom(temp)){
			cout << "ERROR : CAR undefined (eval(s1) is an atom)" << endl;
			exit(0);
		}
		temp->left->type = "Nat";
		return temp->left;
	}
	//CDR
	if(leaf->left->key=="CDR"){
		if (treelength(leaf)!=2)
		{
			cout << "ERROR : CDR undefined (treelength(leaf)!=2)" << endl;
			exit(0);
		}
		struct TreeNode *temp = 0;
		temp = eval(leaf->right->left);
		///////////////TYPE///////////////////
		if (temp->type=="List"&&temp->key=="NIL")
		{
			cout << "ERROR : [Type]CDR input can't be a list that is empty" << endl;
			exit(0);
		}
		if (temp->type!="List")
		{
			cout << "ERROR : [Type]CDR input should be list of numbers" << endl;
			exit(0);
		}
		if (temp->couldbeNIL==true)
		{
			cout << "ERROR : [Type]CDR Static checking found potentially-empty lists" << endl;
			exit(0);
		}
		//////////////////////////////////
		if(is_atom(temp)){
			cout << "ERROR : CDR undefined (eval(s1) is an atom)" << endl;
			exit(0);
		}
		temp->left->type = "List";
		return temp->right;
	}
	//CONS
	if(leaf->left->key=="CONS"){
		if (treelength(leaf)!=3)
		{
			cout << "ERROR : CONS undefined (treelength(leaf)!=3)" << endl;
			exit(0);
		}
		struct TreeNode *temp = NewNode("");
		temp->left = eval(leaf->right->left);
		temp->right = eval(leaf->right->right->left);
		////////////////TYPE//////////////////
		if (temp->left->type!="Nat")
		{
			cout << "ERROR : [Type]CONS input s1 should be number" << endl;
			exit(0);
		}
		if (temp->right->type!="List")
		{
			cout << "ERROR : [Type]CONS input s2 should be a list of number" << endl;
			exit(0);
		}
		//////////////////////////////////
		temp->type = "List";
		return temp;
	}
	//ATOM
	if(leaf->left->key=="ATOM"){
		if (treelength(leaf)!=2)
		{
			cout << "ERROR : ATOM undefined (treelength(leaf)!=2)" << endl;
			exit(0);
		}
		// if(is_atom(eval(leaf->right->left))){
		if(eval(leaf->right->left)->type=="Bool"||eval(leaf->right->left)->type=="Nat"){
			struct TreeNode *temp = NewNode("T");
			temp->type = "Bool";
			return temp;
		}
		else if(eval(leaf->right->left)->type=="List"){
			struct TreeNode *temp = NewNode("F");
			temp->type = "Bool";
			return temp;
		}else{
			cout << "ERROR : [Type]ATOM undefined, input is neither Bool, Nat, or List" << endl;
			exit(0);
		}
	}
	//INT
	if(leaf->left->key=="INT"){
		if (treelength(leaf)!=2)
		{
			cout << "ERROR : INT undefined (treelength(leaf)!=2)" << endl;
			exit(0);
		}
		// if(is_number((eval(leaf->right->left)->key)))
		// 	return NewNode("T");
		// else
		// 	return NewNode("NIL");
		if(eval(leaf->right->left)->type=="Nat"){
			struct TreeNode *temp = NewNode("T");
			temp->type = "Bool";
			return temp;
		}
		else if(eval(leaf->right->left)->type=="Bool"||eval(leaf->right->left)->type=="List"){
			struct TreeNode *temp = NewNode("F");
			temp->type = "Bool";
			return temp;
		}else{
			cout << "ERROR : [Type]INT undefined, input is neither Bool, Nat, or List" << endl;
			exit(0);
		}
	}
	//NULL
	if(leaf->left->key=="NULL"){
		if (treelength(leaf)!=2)
		{
			cout << "ERROR : NULL undefined (treelength(leaf)!=2)" << endl;
			exit(0);
		}
		// if((eval(leaf->right->left))->key == "NIL")
		// 	return NewNode("T");
		// else
		// 	return NewNode("NIL");
		if(eval(leaf->right->left)->type=="List"){
			if (eval(leaf->right->left)->key=="NIL")
			{
				struct TreeNode *temp = NewNode("T");
				temp->type = "Bool";
				return temp;
			}else{
				struct TreeNode *temp = NewNode("F");
				temp->type = "Bool";
				return temp;
			}
		}else{
			cout << "ERROR : [Type]NULL undefined, input should be List" << endl;
			exit(0);
		}
	}
	//EQ
	if(leaf->left->key=="EQ"){
		if (treelength(leaf)!=3)
		{
			cout << "ERROR : EQ undefined (treelength(leaf)!=3)" << endl;
			exit(0);
		}else if(!is_atom(eval(leaf->right->left))){
			cout << "ERROR : eval(s1) is something other than an atom" << endl;
			exit(0);
		}else if(!is_atom(eval(leaf->right->right->left))){
			cout << "ERROR : eval(s2) is something other than an atom" << endl;
			exit(0);
		}
		// if((eval(leaf->right->left))->key == (eval(leaf->right->right->left))->key)
		// 	return NewNode("T");
		// else
		// 	return NewNode("NIL");
		if(eval(leaf->right->left)->type=="Nat"&&eval(leaf->right->right->left)->type=="Nat"){
			if ((eval(leaf->right->left))->key == (eval(leaf->right->right->left))->key)
			{
				struct TreeNode *temp = NewNode("T");
				temp->type = "Bool";
				return temp;
			}else{
				struct TreeNode *temp = NewNode("F");
				temp->type = "Bool";
				return temp;
			}
		}else{
			cout << "ERROR : [Type]EQ undefined, input should be Nat" << endl;
			exit(0);
		}
	}
	//PLUS
	if(leaf->left->key=="PLUS"){
		if (treelength(leaf)!=3)
		{
			cout << "ERROR : PLUS undefined (treelength(leaf)!=3)" << endl;
			exit(0);
		}
		// else if(!is_number((eval(leaf->right->left))->key)){
		// 	cout << "ERROR : PLUS - eval(s1) is something other than an numeric atom " << (eval(leaf->right->left))->key  << endl;
		// 	exit(0);
		// }else if(!is_number( (eval(leaf->right->right->left))->key )){
		// 	cout << "ERROR : PLUS - eval(s2) is something other than an numeric atom " << (eval(leaf->right->right->left))->key << endl;
		// 	exit(0);
		// }
		// return NewNode(to_str( to_int((eval(leaf->right->left))->key)+to_int((eval(leaf->right->right->left))->key) ));
		if(eval(leaf->right->left)->type=="Nat"&&eval(leaf->right->right->left)->type=="Nat"){
			struct TreeNode *temp = NewNode(to_str( to_int((eval(leaf->right->left))->key)+to_int((eval(leaf->right->right->left))->key) ));
			temp->type = "Nat";
			return temp;
		}else{
			cout << "ERROR : [Type]PLUS undefined, inputs should both be Nat" << endl;
			exit(0);
		}
	}
	//MINUS
	// if(leaf->left->key=="MINUS"){
	// 	if (treelength(leaf)!=3)
	// 	{
	// 		cout << "ERROR : MINUS undefined (treelength(leaf)!=3)" << endl;
	// 		exit(0);
	// 	}
	// 	if(eval(leaf->right->left)->type=="Nat"&&eval(leaf->right->right->left)->type=="Nat"){
	// 		struct TreeNode *temp = NewNode(to_str( to_int((eval(leaf->right->left))->key)-to_int((eval(leaf->right->right->left))->key) ));
	// 		temp->type = "Nat";
	// 		return temp;
	// 	}else{
	// 		cout << "ERROR : [Type]MINUS undefined, inputs should both be Nat" << endl;
	// 		exit(0);
	// 	}
	// }
	//TIMES
	// if(leaf->left->key=="TIMES"){
	// 	if (treelength(leaf)!=3)
	// 	{
	// 		cout << "ERROR : TIMES undefined (treelength(leaf)!=3)" << endl;
	// 		exit(0);
	// 	}else if(!is_number((eval(leaf->right->left))->key)){
	// 		cout << "ERROR : TIMES - eval(s1) is something other than an numeric atom " << (eval(leaf->right->left))->key << endl;
	// 		exit(0);
	// 	}else if(!is_number((eval(leaf->right->right->left))->key)){
	// 		cout << "ERROR : TIMES - eval(s2) is something other than an numeric atom " << (eval(leaf->right->right->left))->key  << endl;
	// 		exit(0);
	// 	}
	// 	return NewNode(to_str( to_int((eval(leaf->right->left))->key)*to_int((eval(leaf->right->right->left))->key) ));
	// }
	//LESS
	if(leaf->left->key=="LESS"){
		if (treelength(leaf)!=3)
		{
			cout << "ERROR : LESS undefined (treelength(leaf)!=3)" << endl;
			exit(0);
		}
		// else if(!is_number((eval(leaf->right->left))->key)){
		// 	cout << "ERROR : LESS - eval(s1) is something other than an numeric atom " << (eval(leaf->right->left))->key << endl;
		// 	exit(0);
		// }else if(!is_number((eval(leaf->right->right->left))->key)){
		// 	cout << "ERROR : LESS - eval(s2) is something other than an numeric atom " << (eval(leaf->right->right->left))->key  << endl;
		// 	exit(0);
		// }
		// if(to_int((eval(leaf->right->left))->key)<to_int((eval(leaf->right->right->left))->key))
		// 	return NewNode("T");
		// else
		// 	return NewNode("NIL");
		if(eval(leaf->right->left)->type=="Nat"&&eval(leaf->right->right->left)->type=="Nat"){
			if (to_int((eval(leaf->right->left))->key)<to_int((eval(leaf->right->right->left))->key))
			{
				struct TreeNode *temp = NewNode("T");
				temp->type = "Bool";
				return temp;
			}else{
				struct TreeNode *temp = NewNode("F");
				temp->type = "Bool";
				return temp;
			}
		}else{
			cout << "ERROR : [Type]LESS undefined, inputs should both be Nat" << endl;
			exit(0);
		}
	}
	//GREATER
	// if(leaf->left->key=="GREATER"){
	// 	if (treelength(leaf)!=3)
	// 	{
	// 		cout << "ERROR : GREATER undefined (treelength(leaf)!=3)" << endl;
	// 		exit(0);
	// 	}
	// 	if(eval(leaf->right->left)->type=="Nat"&&eval(leaf->right->right->left)->type=="Nat"){
	// 		if (to_int((eval(leaf->right->left))->key)>to_int((eval(leaf->right->right->left))->key))
	// 		{
	// 			struct TreeNode *temp = NewNode("T");
	// 			temp->type = "Bool";
	// 			return temp;
	// 		}else{
	// 			struct TreeNode *temp = NewNode("F");
	// 			temp->type = "Bool";
	// 			return temp;
	// 		}
	// 	}else{
	// 		cout << "ERROR : [Type]GREATER undefined, inputs should both be Nat" << endl;
	// 		exit(0);
	// 	}
	// }
	//QUOTE
	// if(leaf->left->key=="QUOTE"){
	// 	if (treelength(leaf)!=2)
	// 	{
	// 		cout << "ERROR : QUOTE length != 2" << endl;
	// 		exit(0);
	// 	}
	// 	return leaf->right->left;
	// }
	//COND
	if(leaf->left->key=="COND"){
		if (treelength(leaf)==1){
			cout << "ERROR : COND length can't be 1" << endl;
			exit(0);
		}else if(!si_list(leaf->right)){
			cout << "ERROR : COND - some si is not a list" << endl;
			exit(0);
		}else if(!si_length(leaf->right)){
			cout << "ERROR : COND - some si is a list such that length(si) != 2" << endl;
			exit(0);
		}
		string type = eval(leaf->right->left->right->left)->type;
		struct TreeNode *temp = cond(leaf->right, type);
		temp->couldbeNIL = NILcheck(leaf->right);
		return temp;
	}
	cout << "ERROR: eval undefined " << leaf->left->key << endl;
	exit(0);
}

void pretty(int index){
	if(index==-1)return;
	if(tree[index].key!=""){
		cout << tree[index].key;
		return;
	}
	cout << "(";
	pretty(tree[index].left);
	cout << " . ";
	pretty(tree[index].right);
	cout << ")";
}

void printtree2(struct TreeNode *leaf){
	if(leaf == NULL)return;
	if(leaf->key!=""){
		cout << leaf->key;
		return;
	}
	cout << "(";
	printtree2(leaf->left);
	cout << " . ";
	printtree2(leaf->right);
	cout << ")";
}

void treetotree(struct TreeNode* leaf, int index){
	if(tree[index].left!=-1){
		leaf->left = NewNode(tree[tree[index].left].key);
		treetotree(leaf->left, tree[tree[index].left].index);
	}
	if(tree[index].right!=-1){
		leaf->right = NewNode(tree[tree[index].right].key);
		treetotree(leaf->right, tree[tree[index].right].index);
	}
}

void printlist(struct TreeNode* leaf){ // input MUST not be a single atom
	cout<<"(";
	struct TreeNode* temp=leaf;
	while(temp->left!=NULL){
		if(temp->left->left!=NULL) printlist(temp->left);
		else cout << temp->left->key;
		if(temp->right->key!="NIL") cout << " ";
		temp = temp->right;
	}
	if(temp->key!="NIL"){
		cout << ". " << temp->key << ")";
	}else{
		cout << ")";
	}
}

void treetolist(struct TreeNode* leaf){
	if(leaf->right==NULL){
		cout << leaf->key;
	}else{
		printlist(leaf);
	}
	cout << endl;
}

void Start(){
	Check();
	while(s.Current.Type != "EOF"){
		// instead of simply cout the output, store them at a buff called ss. If there's no error, print out ss. This prevents error message appear in the middle of parsing/scanning.
		treeinit();
		Expr();
		// if the program manages to reach here, means there's no error. Thus print out legal results.
		// pretty(0); // same as cout << ss.str() << endl;
		// cout << endl;

		// ******** Raw tree ********
		//printtree(0);// uncomment to see tree. (my_index,content,back_index,left_index,right_index)
		root = NewNode(tree[0].key);
		treetotree(root, 0);

		// cout << "pretty : ";
		// pretty(0);
		// cout<<endl;

		// cout << "input  : ";
		// printtree2(root);
		// cout << endl;

		// ******************EVAL DISABLED FOR PROJECT 5****************
		// root = eval(root);
		struct TreeNode *dummy = eval(root);
		free(dummy);
		// ******************EVAL DISABLED FOR PROJECT 5****************

		// cout << "output : ";
		// printtree2(root);
		// cout << endl;
		treetolist(root);
	}
}

void Expr(){
	Check();
	if(s.Current.Type == "Atom"){
		fillnode(s.Current.Content);
		s.MoveToNext();
	}
	else if(s.Current.Type == "OpenParenthesis"){
		s.MoveToNext();
		if(s.Current.Type == "ClosingParenthesis"){
			fillnode("NIL");
		}
		while(s.Current.Type != "ClosingParenthesis"){
			List();
		}
		s.MoveToNext();
	}
	else
		s.error = "[syntax error] not expecting \"" + s.Current.Content + "\"";
}

void List(){
	Check();
	int x = 0; // x is for counting how many closing parenthesis needs to be printed according to open parenthesis.
	while(s.Current.Type == "Atom" || s.Current.Type == "OpenParenthesis"){
		x++;
		newnode();
		Expr();
		focusright();
	}
	fillnode("NIL");
	while(x!=0){ // fill up all the forgotten closing parenthesises.
		x--;
		focusback();
	}
}

int main(){
	// myfile.open("graph.dot");
	// myfile << "digraph G {"<<endl;
	s.Init();
	Start();
	// myfile << "}" << endl;
	// myfile.close();
	return 0;
}