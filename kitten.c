#include "kitten.h"

#include <ctype.h>
#include <math.h>
#include <stdarg.h>
#include <stdlib.h>

KClosure** k_closure;
KObject* k_data;
KObject* k_locals;
KCall* k_call;

int k_argc;
char** k_argv;

static KCall* call_bottom;
static KObject* data_bottom;
static KObject* locals_bottom;

static KCall* call_top;
static KObject* data_top;
static KObject* locals_top;
static KClosure** closure_top;

static KObject k_choice_new(KObject, k_cell_t);

static KObject k_get_closed(KClosedName, int);
static KObject k_activation_new_va(void*, va_list);

static KObject k_vector_append_mutating(KObject, KObject);
static KObject k_vector_append_mutating_moving(KObject, KObject);
static KObject k_vector_prepend_mutating(KObject, KObject);
static void k_vector_push(KObject, KObject);
static void k_vector_reserve(KObject, k_cell_t);

int k_object_unique(KObject);

////////////////////////////////////////////////////////////////////////////////
// Runtime initialization.

void k_runtime_init(int argc, char** argv) {

  k_argc = argc;
  k_argv = argv;

  const size_t CLOSURE_SIZE = 1024;
  k_closure = k_mem_alloc(CLOSURE_SIZE, sizeof(KClosure*));
  closure_top = k_closure;
  k_closure += CLOSURE_SIZE;

  const size_t CALL_SIZE = 1024;
  k_call = k_mem_alloc(CALL_SIZE, sizeof(KCall));
  call_top = k_call;
  k_call += CALL_SIZE;
  call_bottom = k_call;

  const size_t DATA_SIZE = 1024;
  k_data = k_mem_alloc(DATA_SIZE, sizeof(KObject));
  data_top = k_data;
  k_data += DATA_SIZE;
  data_bottom = k_data;

  const size_t LOCALS_SIZE = 1024;
  k_locals = k_mem_alloc(LOCALS_SIZE, sizeof(KObject));
  locals_top = k_locals;
  k_locals += LOCALS_SIZE;
  locals_bottom = k_locals;

}

void k_runtime_quit() {
  k_mem_free(closure_top);
  k_data_drop(data_bottom - k_data);
  k_mem_free(data_top);
  k_locals_drop(locals_bottom - k_locals);
  k_mem_free(locals_top);
  k_mem_free(call_top);
}

////////////////////////////////////////////////////////////////////////////////
// Memory and reference counting.

void* k_mem_alloc(const size_t count, const size_t size) {
  void* allocated = calloc(count, size);
  assert(allocated);
  return allocated;
}

void k_mem_free(void* const pointer) {
  free(pointer);
}

void* k_mem_realloc(void* allocated, const size_t count, const size_t size) {
  const size_t bytes = count * size;
  allocated = realloc(allocated, bytes);
  assert(allocated);
  return allocated;
}

void k_object_release(const KObject object) {
  switch (object.type) {
  case K_ACTIVATION:
    {
      KActivation* const activation = object.data.as_activation;
      if (--activation->refs == 0) {
        for (KObject* object = activation->begin;
          object != activation->end; ++object) {
          k_object_release(*object);
        }
        k_mem_free(activation->begin);
        k_mem_free(activation);
      }
      break;
    }
  case K_CHOICE:
    {
      KChoice* const choice = object.data.as_choice;
      if (--choice->refs == 0) {
        k_object_release(choice->value);
        k_mem_free(choice);
      }
      break;
    }
  case K_OPTION:
    {
      KOption* const option = object.data.as_option;
      if (option && --option->refs == 0) {
        k_object_release(option->value);
        k_mem_free(option);
      }
      break;
    }
  case K_PAIR:
    {
      KPair* const pair = object.data.as_pair;
      if (--pair->refs == 0) {
        k_object_release(pair->first);
        k_object_release(pair->rest);
        k_mem_free(pair);
      }
      break;
    }
  case K_VECTOR:
    {
      KVector* const vector = object.data.as_vector;
      if (--vector->refs == 0) {
        const k_cell_t size = vector->end - vector->begin;
        for (k_cell_t i = 0; i < size; ++i)
          k_object_release(vector->begin[i]);
        k_mem_free(vector->begin);
        k_mem_free(vector);
      }
      break;
    }
  case K_USER:
    {
      KUser* const user = object.data.as_user;
      if (--user->refs == 0) {
        for (k_cell_t i = 0; i < user->size; ++i)
          k_object_release(user->fields[i]);
        k_mem_free(user);
      }
    }
  default:
    break;
  }
}

int k_object_unique(const KObject object) {
  return object.type >= K_BOXED ? *object.data.as_refs == 1 : 1;
}

////////////////////////////////////////////////////////////////////////////////
// Value creation.

static KObject k_activation_new_va(void* const target, va_list args) {
  KActivation* const activation = k_mem_alloc(1, sizeof(KActivation));
  activation->refs = 1;
  activation->function = target;
  const size_t size = va_arg(args, size_t);
  activation->begin = k_mem_alloc(size, sizeof(KObject));
  activation->end = activation->begin + size;
  for (size_t i = 0; i < size; ++i) {
    const KClosedName namespace = va_arg(args, KClosedName);
    const int index = va_arg(args, int);
    activation->begin[i] = k_object_retain(k_get_closed(namespace, index));
  }
  return (KObject) {
    .data = (KData) { .as_activation = activation },
    .type = K_ACTIVATION
  };
}

KObject k_activation_new(void* const target, ...) {
  va_list args;
  va_start(args, target);
  const KObject activation = k_activation_new_va(target, args);
  va_end(args);
  return activation;
}

static KObject k_choice_new(const KObject value, const k_cell_t which) {
  KChoice* const data = k_mem_alloc(1, sizeof(KChoice));
  data->refs = 1;
  data->which = which;
  data->value = value;
  return (KObject) {
    .data = (KData) { .as_choice = data },
    .type = K_CHOICE
  };
}

KObject k_left_new(const KObject value) {
  return k_choice_new(value, 0);
}

KObject k_pair_new(const KObject first, const KObject rest) {
  KPair* pair = k_mem_alloc(1, sizeof(KPair));
  pair->refs = 1;
  pair->first = first;
  pair->rest = rest;
  return (KObject) { .data = (KData) { .as_pair = pair }, .type = K_PAIR };
}

KObject k_right_new(const KObject value) {
  return k_choice_new(value, 1);
}

KObject k_some_new(const KObject value) {
  KOption* option = k_mem_alloc(1, sizeof(KOption));
  option->refs = 1;
  option->value = value;
  return (KObject) { .data = (KData) { .as_option = option }, .type = K_OPTION };
}

// Creates a new vector with uninitialized elements.
KObject k_vector_new(const size_t size) {
  KVector* const vector = k_mem_alloc(1, sizeof(KVector));
  vector->refs = 1;
  vector->begin = k_mem_alloc(size, sizeof(KObject));
  vector->end = vector->begin + size;
  vector->capacity = vector->begin + size;
  return (KObject) {
    .data = (KData) { .as_vector = vector },
    .type = K_VECTOR
  };
}

////////////////////////////////////////////////////////////////////////////////
// Vector operations.

// Computes the least power of two not less than 'size'.
static k_cell_t fit_capacity(k_cell_t size) {
  --size;
  size |= size >> 1;
  size |= size >> 2;
  size |= size >> 4;
  size |= size >> 8;
  size |= size >> 16;
  size |= size >> 32;
  return size + 1;
}

KObject k_vector_append(const KObject a, const KObject b) {
  const k_cell_t size = k_vector_size(a) + k_vector_size(b);
  const KObject vector = k_vector_new(size);
  const KObject* from = a.data.as_vector->begin;
  KObject* to = vector.data.as_vector->begin;
  const KObject* const a_end = a.data.as_vector->end;
  while (from != a_end)
    *to++ = k_object_retain(*from++);
  from = b.data.as_vector->begin;
  const KObject* const b_end = b.data.as_vector->end;
  while (from != b_end)
    *to++ = k_object_retain(*from++);
  assert(to == vector.data.as_vector->end);
  return vector;
}

static KObject k_vector_append_mutating(const KObject a, const KObject b) {
  const k_cell_t size_a = k_vector_size(a);
  const k_cell_t size_b = k_vector_size(b);
  const k_cell_t total_size = size_a + size_b;
  k_vector_reserve(a, fit_capacity(total_size));
  const KObject* from = b.data.as_vector->begin;
  const KObject* const b_end = b.data.as_vector->end;
  while (from != b_end)
    k_vector_push(a, k_object_retain(*from++));
  return a;
}

static KObject k_vector_append_mutating_moving
  (const KObject a, const KObject b) {
  const k_cell_t size_a = k_vector_size(a);
  const k_cell_t size_b = k_vector_size(b);
  const k_cell_t total_size = size_a + size_b;
  k_vector_reserve(a, fit_capacity(total_size));
  KObject* from = b.data.as_vector->begin;
  const KObject* const b_end = b.data.as_vector->end;
  while (from != b_end) {
    k_vector_push(a, *from);
    *from++ = k_unit_new();
  }
  return a;
}

static KObject k_vector_prepend_mutating(const KObject a, const KObject b) {
  const k_cell_t size_a = k_vector_size(a);
  const k_cell_t size_b = k_vector_size(b);
  const k_cell_t total_size = size_a + size_b;
  k_vector_reserve(b, fit_capacity(total_size));
  KVector* const vector = b.data.as_vector;
  memmove(
    vector->begin + size_a,
    vector->begin,
    (vector->end - vector->begin) * sizeof(KObject));
  vector->end = vector->begin + total_size;
  KObject* to = vector->begin;
  const KObject* from = a.data.as_vector->begin;
  const KObject* const a_end = a.data.as_vector->end;
  while (from != a_end)
    *to++ = k_object_retain(*from++);
  return b;
}

static void k_vector_push(const KObject object, const KObject value) {
  assert(object.type == K_VECTOR);
  KVector* const vector = object.data.as_vector;
  if (vector->end == vector->capacity)
    k_vector_reserve(object, fit_capacity(vector->end - vector->begin + 1));
  *vector->end++ = value;
}

static void k_vector_reserve(const KObject object, const k_cell_t capacity) {
  assert(object.type == K_VECTOR);
  KVector* const vector = object.data.as_vector;
  if (vector->begin + capacity <= vector->capacity)
    return;
  const k_cell_t size = vector->end - vector->begin;
  vector->begin = k_mem_realloc
    (vector->begin, capacity, sizeof(KObject));
  vector->end = vector->begin + size;
  vector->capacity = vector->begin + capacity;
}

KObject k_vector(const size_t size, ...) {
  va_list args;
  va_start(args, size);
  KVector* const vector = k_mem_alloc(1, sizeof(KVector));
  vector->refs = 1;
  vector->begin = k_mem_alloc(size, sizeof(KObject));
  vector->end = vector->begin + size;
  vector->capacity = vector->begin + size;
  for (size_t i = 0; i < size; ++i) {
    vector->begin[i] = va_arg(args, KObject);
  }
  va_end(args);
  return (KObject) {
    .data = (KData) { .as_vector = vector },
    .type = K_VECTOR
  };
}

KObject k_vector_get(const KObject object, k_cell_t index) {
  assert(object.type == K_VECTOR);
  assert(k_vector_size(object) > index);
  const KVector* const vector = object.data.as_vector;
  return vector->begin[index];
}

void k_vector_set(const KObject object, k_cell_t index, const KObject value) {
  assert(object.type == K_VECTOR);
  const KVector* const vector = object.data.as_vector;
  vector->begin[index] = value;
}

k_cell_t k_vector_size(const KObject object) {
  assert(object.type == K_VECTOR);
  const KVector* const vector = object.data.as_vector;
  return vector->end - vector->begin;
}

////////////////////////////////////////////////////////////////////////////////
// Intrinsics.

static KObject k_get_closed(const KClosedName namespace, const int index) {
  switch (namespace) {
  case K_CLOSED:
    return k_locals_get(index);
  case K_RECLOSED:
    return k_closure_get(index);
  default:
    K_ASSERT_IMPOSSIBLE();
  }
}

void k_in_add_vector() {
  KObject b = k_data_pop();
  KObject a = k_data_pop();
  assert(a.type == K_VECTOR);
  assert(b.type == K_VECTOR);
  const int unique_a = k_object_unique(a);
  const int unique_b = k_object_unique(b);
  if (unique_a && unique_b) {
    k_data_push(k_vector_append_mutating_moving(a, b));
    k_object_release(b);
  } else if (unique_a) {
    k_data_push(k_vector_append_mutating(a, b));
    k_object_release(b);
  } else if (unique_b) {
    k_data_push(k_vector_prepend_mutating(a, b));
    k_object_release(a);
  } else {
    k_data_push(k_vector_append(a, b));
    k_object_release(a);
    k_object_release(b);
  }
}

void k_in_char_to_int() {
  const KObject a = k_data_pop();
  assert(a.type == K_CHAR);
  k_data_push((KObject) {
    .data = (KData) { .as_int = a.data.as_char },
    .type = K_INT
  });
}

void k_in_close() {
  KObject handle = k_data_pop();
  assert(handle.type == K_HANDLE);
  fclose(handle.data.as_handle);
}

void k_in_construct(const k_cell_t tag, size_t size) {
  KUser* user = k_mem_alloc(1, 3 * sizeof(k_cell_t) + size * sizeof(KObject));
  user->refs = 1;
  user->tag = tag;
  user->size = size;
  while (size)
    user->fields[--size] = k_data_pop();
  k_data_push((KObject) {
    .data = (KData) { .as_user = user },
    .type = K_USER
  });
}

void k_in_first() {
  const KObject a = k_data_pop();
  assert(a.type == K_PAIR);
  k_data_push(k_object_retain(a.data.as_pair->first));
  k_object_release(a);
}

void k_in_float_to_int() {
  const KObject a = k_data_pop();
  assert(a.type == K_FLOAT);
  k_data_push(k_some_new((KObject) {
    .data = (KData) { .as_int = a.data.as_float },
    .type = K_INT
  }));
}

void k_in_from_left() {
  const KObject a = k_data_pop();
  assert(a.type == K_CHOICE && a.data.as_choice->which == 0);
  k_data_push(k_object_retain(a.data.as_choice->value));
  k_object_release(a);
}

void k_in_from_right() {
  const KObject a = k_data_pop();
  assert(a.type == K_CHOICE && a.data.as_choice->which == 1);
  k_data_push(k_object_retain(a.data.as_choice->value));
  k_object_release(a);
}

void k_in_from_some() {
  const KObject a = k_data_pop();
  assert(a.type == K_OPTION && a.data.as_option);
  k_data_push(k_object_retain(a.data.as_option->value));
  k_object_release(a);
}

void k_in_get() {
  const KObject index = k_data_pop();
  assert(index.type == K_INT);
  const KObject vector = k_data_pop();
  assert(vector.type == K_VECTOR);
  const k_cell_t i = (k_cell_t)index.data.as_int;
  const k_cell_t size = k_vector_size(vector);
  k_data_push(i >= size
    ? k_none_new() : k_some_new(k_object_retain(k_vector_get(vector, i))));
  k_object_release(vector);
}

void k_in_get_line() {
  KObject handle = k_data_pop();
  assert(handle.type == K_HANDLE);
  size_t length = 1;
  char line[1024];
  if (fgets(line, 1024, handle.data.as_handle))
    length = strlen(line);
  const KObject string = k_vector_new(length - 1);
  for (size_t i = 0; i < length - 1; ++i)
    k_vector_set(string, i, k_char_new(line[i]));
  k_data_push(string);
}

void k_in_init() {
  const KObject vector = k_data_pop();
  assert(vector.type == K_VECTOR);
  const k_cell_t size = k_vector_size(vector);
  const KObject result = k_vector_new(size == 0 ? 0 : size - 1);
  for (k_cell_t i = 0; i + 1 < size; ++i)
    k_vector_set(result, i, k_object_retain(k_vector_get(vector, i)));
  k_data_push(result);
  k_object_release(vector);
}

void k_in_int_to_char() {
  const KObject a = k_data_pop();
  assert(a.type == K_INT);
  k_data_push((KObject) {
    .data = (KData) { .as_char = a.data.as_int },
    .type = K_CHAR
  });
}

void k_in_int_to_float() {
  const KObject a = k_data_pop();
  assert(a.type == K_INT);
  k_data_push(k_some_new((KObject) {
    .data = (KData) { .as_float = a.data.as_int },
    .type = K_FLOAT
  }));
}

void k_in_left() {
  const KObject left = k_left_new(k_data_pop());
  k_data_push(left);
}

void k_in_length() {
  const KObject vector = k_data_pop();
  assert(vector.type == K_VECTOR);
  k_data_push(k_int_new(k_vector_size(vector)));
  k_object_release(vector);
}

void k_in_make_vector(const size_t size) {
  KVector* const vector = k_mem_alloc(1, sizeof(KVector));
  vector->refs = 1;
  vector->begin = k_mem_alloc(size, sizeof(KObject));
  vector->end = vector->begin + size;
  vector->capacity = vector->begin + size;
  // Moving from stack into vector; no retain/release needed.
  for (size_t i = 0; i < size; ++i)
    vector->begin[i] = k_data[size - i - 1];
  k_data += size;
  k_data_push((KObject) {
    .data = (KData) { .as_vector = vector },
    .type = K_VECTOR
  });
}

void k_in_match(const size_t size, ...) {
  va_list args;
  va_start(args, size);
  const KObject scrutinee = k_data_pop();
  assert(scrutinee.type == K_USER);
  for (size_t i = 0; i < size; ++i) {
    const k_cell_t tag = va_arg(args, k_cell_t);
    void* const target = va_arg(args, void*);
    if (tag == scrutinee.data.as_user->tag) {
      const KObject activation = k_activation_new_va(target, args);
      va_end(args);
      for (size_t j = 0; j < scrutinee.data.as_user->size; ++j)
        k_data_push(k_object_retain(scrutinee.data.as_user->fields[j]));
      k_object_release(scrutinee);
      k_data_push(activation);
      return;
    }
    int closure_size = va_arg(args, int);
    for (int j = 0; j < closure_size; ++j) {
      va_arg(args, KClosedName);
      va_arg(args, int);
    }
  }
  k_object_release(scrutinee);
  void* const default_case = va_arg(args, void*);
  if (!default_case) {
    fprintf(stderr, "pattern match failure\n");
    exit(1);
  }
  const KObject activation = k_activation_new_va(default_case, args);
  va_end(args);
  k_data_push(activation);
}

void k_in_mod_float() {
  const KObject b = k_data_pop();
  const KObject a = k_data_pop();
  assert(a.type == b.type && a.type == K_FLOAT);
  const k_float_t result = fmod(a.data.as_float, b.data.as_float);
  k_data_push(k_float_new(result));
}

void k_in_pair() {
  const KObject b = k_data_pop();
  const KObject a = k_data_pop();
  k_data_push(k_pair_new(a, b));
}

void k_in_pow_float() {
  const KObject b = k_data_pop();
  const KObject a = k_data_pop();
  assert(a.type == b.type && a.type == K_FLOAT);
  const k_float_t result = pow(a.data.as_float, b.data.as_float);
  k_data_push(k_float_new(result));
}

void k_in_print() {
  const KObject handle = k_data_pop();
  assert(handle.type == K_HANDLE);
  const KObject string = k_data_pop();
  assert(string.type == K_VECTOR);
  for (KObject* character = string.data.as_vector->begin;
    character != string.data.as_vector->end; ++character) {
    fputc(character->data.as_char, handle.data.as_handle);
  }
  k_object_release(string);
}

void k_in_rest() {
  const KObject a = k_data_pop();
  assert(a.type == K_PAIR);
  k_data_push(k_object_retain(a.data.as_pair->rest));
  k_object_release(a);
}

void k_in_right() {
  const KObject right = k_right_new(k_data_pop());
  k_data_push(right);
}

void k_in_set() {
  const KObject value = k_data_pop();
  const KObject index = k_data_pop();
  assert(index.type == K_INT);
  assert(k_data[0].type == K_VECTOR);
  if (k_object_unique(k_data[0])) {
    k_vector_set(k_data[0], index.data.as_int, value);
  } else {
    const KObject vector = k_data_pop();
    const k_cell_t size = k_vector_size(vector);
    const KObject result = k_vector_new(size);
    for (k_cell_t i = 0; i < size; ++i) {
      if (i == (k_cell_t)index.data.as_int) {
        k_vector_set(result, i, value);
        continue;
      }
      k_vector_set(result, i, k_object_retain(k_vector_get(vector, i)));
    }
    k_object_release(vector);
    k_data_push(result);
  }
}

void k_in_show_float() {
  const KObject x = k_data_pop();
  assert(x.type == K_FLOAT);
  char buffer[
    1  // sign
    + (DBL_MAX_10_EXP + 1)  // decimal digits
    + 1  // dot
    + 6  // default precision
    + 1  // null
  ];
  int length = 0;
  snprintf(buffer, sizeof(buffer),
    "%f%n", x.data.as_float, &length);
  const KObject string = k_vector_new(length);
  for (size_t i = 0; i < (size_t)length; ++i)
    k_vector_set(string, i, k_char_new(buffer[i]));
  k_data_push(string);
}

void k_in_show_int() {
  const KObject x = k_data_pop();
  assert(x.type == K_INT);
  char buffer[20] = {0};
  int length = 0;
  snprintf(buffer, sizeof(buffer),
    "%"PRId64"%n", x.data.as_int, &length);
  const KObject string = k_vector_new(length);
  for (size_t i = 0; i < (size_t)length; ++i)
    k_vector_set(string, i, k_char_new(buffer[i]));
  k_data_push(string);
}

void k_in_some() {
  KObject some = k_some_new(k_data_pop());
  k_data_push(some);
}

void k_in_tail() {
  const KObject vector = k_data_pop();
  assert(vector.type == K_VECTOR);
  const k_cell_t size = k_vector_size(vector);
  const KObject result = k_vector_new(size == 0 ? 0 : size - 1);
  for (k_cell_t i = 0; i + 1 < size; ++i)
    k_vector_set(result, i, k_object_retain(k_vector_get(vector, i + 1)));
  k_data_push(result);
  k_object_release(vector);
}
