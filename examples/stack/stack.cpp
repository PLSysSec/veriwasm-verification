#include <iostream>
#include <vector>
#include <cstdlib>
#include <string>
#include <stdexcept>

using namespace std;

template <class T>
class Stack { 
   private: 
      T elems[10];    // elements 
			unsigned short int i = 0;

   public: 
      void push(T const&);  // push element 
      void pop();               // pop element 
      T top() const;            // return top element 
      
      bool empty() const {      // return true if empty.
         return elems.empty(); 
      } 
}; 

template <class T>
void Stack<T>::push (T const& elem) { 
   // append copy of passed element 
   elems[i] = elem;
	i++;
} 

template <class T>
void Stack<T>::pop () { 
   if (i != 0) { 
			i--;
   }
} 

template <class T>
T Stack<T>::top () const { 
   if (i != 0) { 
   return elems[i-1];
   }
	 else elems[0];
} 

int main() { 
   try {
      Stack<int>         intStack;  // stack of ints 
      // manipulate int stack 
      intStack.push(7); 
      cout << intStack.top() <<endl; 
			intStack.pop();
   } catch (exception const& ex) { 
      cerr << "Exception: " << ex.what() <<endl; 
      return -1;
   } 
} 

