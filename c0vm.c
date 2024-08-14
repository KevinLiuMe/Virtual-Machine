/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2023                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

#include "lib/xalloc.h"
#include "lib/stack.h"
#include "lib/contracts.h"
#include "lib/c0v_stack.h"
#include "lib/c0vm.h"
#include "lib/c0vm_c0ffi.h"
#include "lib/c0vm_abort.h"

/* call stack frames */
typedef struct frame_info frame;
struct frame_info {
  c0v_stack_t  S;   /* Operand stack of C0 values */
  ubyte       *P;   /* Function body */
  size_t       pc;  /* Program counter */
  c0_value    *V;   /* The local variables */
};

void push_int(c0v_stack_t S, int i){
  REQUIRES(S!=NULL);
  c0v_push(S, int2val(i));
  ENSURES(!c0v_stack_empty(S));
}

void* pop_ptr(c0v_stack_t S){
  return val2ptr(c0v_pop(S));
}

void push_ptr(c0v_stack_t S, void *x)
{
  c0v_push(S, ptr2val(x));
}

int execute(struct bc0_file *bc0) {
  REQUIRES(bc0 != NULL);

  c0v_stack_t S = c0v_stack_new();
  ENSURES(S!=NULL);

  ubyte *P = bc0->function_pool[0].code;

  size_t pc = 0;

  size_t num_vars = bc0->function_pool[0].num_vars;
  c0_value *V = xcalloc(sizeof(c0_value), num_vars);

  (void) V; 
  
  gstack_t callStack = stack_new();

  (void) callStack;


  while (true) {

#ifdef DEBUG
    /* You can add extra debugging information here */
    fprintf(stderr, "Opcode %x -- Stack size: %zu -- PC: %zu\n",
            P[pc], c0v_stack_size(S), pc);
#endif

    switch (P[pc]) {

    /* Additional stack operation: */

    case POP: {
      pc++;
      c0v_pop(S);
      break;
    }

    case DUP: {
      pc++;
      c0_value v = c0v_pop(S);
      c0v_push(S,v);
      c0v_push(S,v);
      break;
    }

    case SWAP: {
      pc++;
      c0_value v_1 = c0v_pop(S);
      c0_value v_2 = c0v_pop(S);
      c0v_push(S, v_1);
      c0v_push(S, v_2);
      break;
    }

    /* Returning from a function.
     * This currently has a memory leak! You will need to make a slight
     * change for the initial tasks to avoid leaking memory.  You will
     * need to revise it further when you write INVOKESTATIC. */

    case RETURN: {
      c0_value retval = c0v_pop(S);
      ASSERT(c0v_stack_empty(S));
      // Another way to print only in DEBUG mode
      IF_DEBUG(fprintf(stderr, 
                        "Returning %d from execute()\n", val2int(retval)));
      c0v_stack_free(S);
      free(V);
      if (stack_empty(callStack)) 
      {
        stack_free(callStack, NULL);
        return val2int(retval);
      }
      else
      {
        frame* fun = (frame*)pop(callStack);
        S = fun->S;
        P = fun->P;
        V = fun->V;
        pc = fun->pc;
        free(fun);
        c0v_push(S, retval);
        break;
      }
    }

    /* Arithmetic and Logical operations */
    case IADD:{
      REQUIRES(c0v_stack_size(S) >= 2);
      pc++;
      c0_value v_1_tmp = c0v_pop(S);
      int32_t v_1 = val2int(v_1_tmp);
      c0_value v_2_tmp = c0v_pop(S);
      int32_t v_2 = val2int(v_2_tmp);
      push_int(S, v_2+v_1);
      ASSERT(!c0v_stack_empty(S));
      break;
    }

    case ISUB:{
      REQUIRES(c0v_stack_size(S) >= 2);
      pc++;
      c0_value v_1_tmp = c0v_pop(S);
      int32_t v_1 = val2int(v_1_tmp);
      c0_value v_2_tmp = c0v_pop(S);
      int32_t v_2 = val2int(v_2_tmp);
      push_int(S, v_2-v_1);
      ASSERT(!c0v_stack_empty(S));
      break;
    }

    case IMUL:{
      REQUIRES(c0v_stack_size(S) >= 2);
      pc++;
      c0_value v_1_tmp = c0v_pop(S);
      int32_t v_1 = val2int(v_1_tmp);
      c0_value v_2_tmp = c0v_pop(S);
      int32_t v_2 = val2int(v_2_tmp);
      push_int(S, v_2*v_1);
      ASSERT(!c0v_stack_empty(S));
      break;
    }

    case IDIV:{
      REQUIRES(c0v_stack_size(S) >= 2);
      pc++;
      c0_value v_1_tmp = c0v_pop(S);
      int32_t v_1 = val2int(v_1_tmp);
      c0_value v_2_tmp = c0v_pop(S);
      int32_t v_2 = val2int(v_2_tmp);
      if(v_2 == INT_MIN && v_1 == -1)
        c0_arith_error("dividing int_min by -1");
      else if (v_1 == 0)
        c0_arith_error("dividing by zero");
      push_int(S, v_2/v_1);
      ASSERT(!c0v_stack_empty(S));
      break;
    }

    case IREM:{
      REQUIRES(c0v_stack_size(S) >= 2);
      pc++;
      c0_value v_1_tmp = c0v_pop(S);
      int32_t v_1 = val2int(v_1_tmp);
      c0_value v_2_tmp = c0v_pop(S);
      int32_t v_2 = val2int(v_2_tmp);
      if(v_2 == INT_MIN && v_1 == -1)
        c0_arith_error("dividing int_min by -1");
      else if (v_1 == 0)
        c0_arith_error("dividing by zero");
      push_int(S, v_2%v_1);
      ASSERT(!c0v_stack_empty(S));
      break;
    }

    case IAND:{
      REQUIRES(c0v_stack_size(S) >= 2);
      pc++;
      c0_value v_1_tmp = c0v_pop(S);
      int32_t v_1 = val2int(v_1_tmp);
      c0_value v_2_tmp = c0v_pop(S);
      int32_t v_2 = val2int(v_2_tmp);
      push_int(S, v_2&v_1);
      ASSERT(!c0v_stack_empty(S));
      break;
    }

    case IOR:{
      REQUIRES(c0v_stack_size(S) >= 2);
      pc++;
      c0_value v_1_tmp = c0v_pop(S);
      int32_t v_1 = val2int(v_1_tmp);
      c0_value v_2_tmp = c0v_pop(S);
      int32_t v_2 = val2int(v_2_tmp);
      push_int(S, v_2|v_1);
      ASSERT(!c0v_stack_empty(S));
      break;
    }

    case IXOR:{
      REQUIRES(c0v_stack_size(S) >= 2);
      pc++;
      c0_value v_1_tmp = c0v_pop(S);
      int32_t v_1 = val2int(v_1_tmp);
      c0_value v_2_tmp = c0v_pop(S);
      int32_t v_2 = val2int(v_2_tmp);
      push_int(S, v_2^v_1);
      ASSERT(!c0v_stack_empty(S));
      break;
    }

    case ISHR:{
      REQUIRES(c0v_stack_size(S) >= 2);
      pc++;
      int32_t v_1 = val2int(c0v_pop(S));
      int32_t v_2 = val2int(c0v_pop(S));
      if (v_1 < 0 || v_1 > 31)
        c0_arith_error("invalid shift to right");
      int32_t res = v_2 >> v_1;
      push_int(S, res);
      ASSERT(!c0v_stack_empty(S));
      break;
    }

    case ISHL:{
      REQUIRES(c0v_stack_size(S) >= 2);
      pc++;
      int32_t v_1 = val2int(c0v_pop(S));
      int32_t v_2 = val2int(c0v_pop(S));
      if (v_1 < 0 || v_1 > 31)
        c0_arith_error("invalid shift to left");
      int32_t res = v_2 << v_1;
      push_int(S, res);
      ASSERT(!c0v_stack_empty(S));
      break;
    }
    /* Pushing constants */

    case BIPUSH:{
      int8_t signed_byte = P[pc+1];
      int32_t tmp = (int32_t)signed_byte;
			push_int(S, tmp);
			pc += 2;
      ASSERT(!c0v_stack_empty(S));
      break;
    }

    case ILDC:{
      uint16_t tmp = ((uint16_t)P[pc+1] << 8) | (uint16_t)P[pc+2];
      int tmp_int = bc0->int_pool[tmp];
      push_int(S, tmp_int);
			pc += 3;
      break;
    }


    case ALDC:{
      uint16_t tmp = ((uint16_t)P[pc+1] << 8) | (uint16_t)P[pc+2];
      c0v_push(S, ptr2val(&bc0->string_pool[tmp]));
      pc+=3;
      break;
    }

    case ACONST_NULL:{
      pc++;
      c0v_push(S, ptr2val(NULL));
      //ASSERT(!c0v_stack_empty(S));
      break;
    }


    /* Operations on local variables */

    case VLOAD:{
      c0v_push(S, V[P[pc+1]]);
      pc+=2;
      ASSERT(S!=NULL);
      break;
    }

    case VSTORE:{
      V[P[pc+1]] = c0v_pop(S);
      pc+=2;
      break;
    }

    /* Assertions and errors */

    case ATHROW:{
      c0_user_error((char*)pop_ptr(S));
			pc++;
      break;
    }

    case ASSERT:{
      void* err = pop_ptr(S);
      int tmp = val2int(c0v_pop(S));
      if(tmp==0){
        c0_assertion_failure((char*)err);
        pc++;
      }
      else{
        pc++;
      }
      break;
    }


    /* Control flow operations */

    case NOP:{
      pc++;
      break;
    }

    case IF_CMPEQ:{
      pc++;
      c0_value tmp_1 = c0v_pop(S);
      c0_value tmp_2 = c0v_pop(S);
      if(val_equal(tmp_1, tmp_2)){
        uint16_t  v_1 = (uint16_t)(P[pc]) << 8;
        pc++;
        uint16_t v_2 = (uint16_t) P[pc];
        uint16_t tmp =  v_1 | v_2;
        int16_t idx = (int16_t) tmp;
        pc += idx - 2;
        break;
      }
      else{
        pc+=2;
      }
      break;
    }

    case IF_CMPNE:{
      pc++;
      c0_value tmp_1 = c0v_pop(S);
      c0_value tmp_2 = c0v_pop(S);
      if(!val_equal(tmp_1, tmp_2)){
        uint16_t  v_1 = (uint16_t)(P[pc]) << 8;
        pc++;
        uint16_t v_2 = (uint16_t) P[pc];
        uint16_t tmp =  v_1 | v_2;
        int16_t idx = (int16_t) tmp;
        pc += idx - 2;
        break; 
      }
      else{
        pc+=2;
      }
      break;
    }

    case IF_ICMPLT:{
      pc++;
      int tmp_1 = val2int(c0v_pop(S));
      int tmp_2 = val2int(c0v_pop(S));
      if(tmp_2 < tmp_1){
        uint16_t  v_1 = (uint16_t)(P[pc]) << 8;
        pc++;
        uint16_t v_2 = (uint16_t) P[pc];
        uint16_t tmp =  v_1 | v_2;
        int16_t idx = (int16_t) tmp;
        pc += idx - 2;
        break; 
      }
      else{
        pc+=2;
      }
      break;
    }

    case IF_ICMPGE:{
      pc++;
      int tmp_1 = val2int(c0v_pop(S));
      int tmp_2 = val2int(c0v_pop(S));
      if(tmp_2 >= tmp_1){
        uint16_t  v_1 = (uint16_t)(P[pc]) << 8;
        pc++;
        uint16_t v_2 = (uint16_t) P[pc];
        uint16_t tmp =  v_1 | v_2;
        int16_t idx = (int16_t) tmp;
        pc += idx - 2;
        break; 
      }
      else{
        pc+=2;
      }
      break;
    }

    case IF_ICMPGT:{
      pc++;
      int tmp_1 = val2int(c0v_pop(S));
      int tmp_2 = val2int(c0v_pop(S));
      if(tmp_2 > tmp_1){
        uint16_t  v_1 = (uint16_t)(P[pc]) << 8;
        pc++;
        uint16_t v_2 = (uint16_t) P[pc];
        uint16_t tmp =  v_1 | v_2;
        int16_t idx = (int16_t) tmp;
        pc += idx - 2;
        break; 
      }
      else{
        pc+=2;
      }
      break;
    }

    case IF_ICMPLE:{
      pc++;
      int tmp_1 = val2int(c0v_pop(S));
      int tmp_2 = val2int(c0v_pop(S));
      if(tmp_2 <= tmp_1){
        uint16_t  v_1 = (uint16_t)(P[pc]) << 8;
        pc++;
        uint16_t v_2 = (uint16_t) P[pc];
        uint16_t tmp =  v_1 | v_2;
        int16_t idx = (int16_t) tmp;
        pc += idx - 2;
        break; 
      }
      else{
        pc+=2;
      }
      break;
    }

    case GOTO:{
      pc++;
      uint16_t  v_1 = (uint16_t)(P[pc]) << 8;
      pc++;
      uint16_t v_2 = (uint16_t) P[pc];
      uint16_t tmp =  v_1 | v_2;
      int16_t idx = (int16_t) tmp;
      pc += idx - 2;
      break;
    }


    /* Function call operations: */

    case INVOKESTATIC:{

      uint8_t v_1 = P[pc+1];
      uint8_t v_2 = P[pc+2];
      uint16_t tmp_0_1 = (uint16_t)(v_1);
      uint16_t tmp_1 = (uint16_t)(v_2);
      uint16_t tmp_0 = tmp_0_1 << 8;
      uint16_t idx = tmp_1 | tmp_0;

      uint16_t v_3 = bc0->function_pool[idx].num_args;
      int i = 0;

      frame *curr_fun = xcalloc(sizeof(frame),1);
			curr_fun->S = S;
			curr_fun->P = P;
			curr_fun->V = V;
      curr_fun->pc = pc + 3;
			push(callStack, (void*)curr_fun);

      S = c0v_stack_new();
			P = bc0->function_pool[idx].code;
			pc = 0;
			V = xcalloc(sizeof(c0_value) * (bc0->function_pool[idx].num_vars), 1);
			for (i = v_3 - 1; i >= 0; i--) {
				V[i] = c0v_pop(curr_fun->S);
      }
      break;

    }

    case INVOKENATIVE:{

      uint8_t v_1 = P[pc+1];
      uint8_t v_2 = P[pc+2];
      uint16_t tmp_0_1 = (uint16_t)(v_1);
      uint16_t tmp_1 = (uint16_t)(v_2);
      uint16_t tmp_0 = tmp_0_1 << 8;
      uint16_t idx = tmp_1 | tmp_0;

      int v_3 = (int)bc0->native_pool[idx].num_args;

      c0_value* args = xcalloc(sizeof(c0_value), v_3);
			int i = 0;

			for (i = v_3 - 1; i >= 0; i--) {
				args[i] = c0v_pop(S);
			}
			
			c0_value res = native_function_table
                      [bc0->native_pool[idx].function_table_index](args);
			c0v_push(S, res);
			
      free(args);
			pc += 3;
			break;

    }

    /* Memory allocation and access operations: */

    case NEW:{
      pc++;
      uint8_t tmp_1 = P[pc];
      char* ptr = xcalloc(sizeof(char),tmp_1);
      push_ptr(S, ptr);
      pc++;
      break;
    }

    case IMLOAD:{
      void* tmp = pop_ptr(S);
      int *int_ptr = (int*)tmp;
			if (int_ptr == NULL)
				c0_memory_error("Segmentation fault");
      push_int(S, *int_ptr);
			pc++;
      break;
    }

    case IMSTORE:{
      c0_value tmp_1 = c0v_pop(S);
      c0_value tmp_2 = c0v_pop(S);
      int *int_ptr = val2ptr(tmp_2);
			if (int_ptr == NULL)
				c0_memory_error("Segmentation fault");
			*int_ptr = val2int(tmp_1);
			pc++;
      break;
    }

    case AMLOAD:{
      c0_value tmp = c0v_pop(S);
      void **ptr = val2ptr(tmp);
      if (ptr == NULL) 
        c0_memory_error("Segmentation fault");
      void *res = *ptr;
      push_ptr(S, res);
      pc++;
      break;
    }

    case AMSTORE:{
      void *ptr_1 = pop_ptr(S);
      void **ptr_2 = pop_ptr(S);
      if (ptr_1 == NULL || ptr_2 == NULL) 
        c0_memory_error("Segmentation fault");
      *ptr_2 = ptr_1;
      pc++;
      break;
    }

    case CMLOAD:{
      c0_value tmp = c0v_pop(S);
      void* int_ptr = val2ptr(tmp);
      if (int_ptr == NULL) 
        c0_memory_error("Segmentation fault");
      int32_t res = (int32_t)*(char*)(int_ptr);
      push_int(S, res);
      pc++;
      break;
    }

    case CMSTORE:{
      int32_t res = val2int(c0v_pop(S));
      void* ptr = val2ptr(c0v_pop(S));
      if(ptr == NULL)
        c0_memory_error("Segmentation fault");
      *(char*)ptr = res & 0x7f;
      break;
    }

    case AADDF:{
      pc++;
      ubyte v_1 = (ubyte)P[pc];
      void* tmp = pop_ptr(S);
      char *char_ptr = (char*)tmp;
      if (char_ptr == NULL) 
        c0_memory_error("Segmentation fault");
      void* res = (void*)(char_ptr+v_1);
      push_ptr(S, res);
      pc++;
      break;
    }


    /* Array operations: */

    case NEWARRAY:{
      pc++;
      int8_t tmp = (int8_t)P[pc];
      int elt_size = (int)tmp;
      int count = val2int(c0v_pop(S));
      if(count<0)
        c0_assertion_failure("size is negative");
      c0_array* res = xcalloc(sizeof(c0_array),1);
      res->count = count;
      res->elems = xcalloc(sizeof(void*),count);
      res->elt_size = elt_size;
      void* ptr = (void*)res;
      push_ptr(S, ptr);
      pc++;
      break;
    }

    case ARRAYLENGTH:{
      void* tmp = pop_ptr(S);
      c0_array* res = (c0_array*) tmp;
      if (res == NULL) 
        c0_memory_error("Segmentation fault");
      push_int(S, res->count);
      pc++;
      break;
    }

    case AADDS:{
      int i = val2int(c0v_pop(S));
      void* tmp = pop_ptr(S);
      c0_array* array = (c0_array*)tmp;
      if (i >= (int)array->count && i >= 0) 
        c0_memory_error("invalid index");
      char *c = (char*)array->elems;
      void *res = (c + (array->elt_size) * i);
      push_ptr(S, res);
      pc++;
      break;
    }


    /* BONUS -- C1 operations */

    case CHECKTAG:

    case HASTAG:

    case ADDTAG:

    case ADDROF_STATIC:

    case ADDROF_NATIVE:

    case INVOKEDYNAMIC:

    default:
      fprintf(stderr, "invalid opcode: 0x%02x\n", P[pc]);
      abort();
    }
  }

  /* cannot get here from infinite loop */
  assert(false);
}
