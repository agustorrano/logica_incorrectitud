#include <stdio.h>
#include <stdlib.h>

typedef struct {
    int id;
    double score;
} Task;

typedef struct {
    Task *items;
    size_t size;
    size_t capacity;
} TaskQueue;

void queue_init(TaskQueue *q) {
    q->items = malloc(sizeof(Task) * 4);
    q->size = 0;
    q->capacity = 4;
}

Task *queue_push(TaskQueue *q, int id, double score) {
    if (q->size == q->capacity) {
        q->capacity *= 2;
        q->items = realloc(q->items, sizeof(Task) * q->capacity);
    }
    Task *slot = &q->items[q->size++];
    slot->id = id;
    slot->score = score;
    return slot;
}

void queue_free(TaskQueue *q) {
    free(q->items);
    q->items = NULL;
    q->size = q->capacity = 0;
}

void apply_catchup_bonus(TaskQueue *q) {
    double total = 0;
    for (size_t i = 0; i < q->size; i++) total += q->items[i].score;
    double avg = q->size ? total / q->size : 0;

    Task *lowest = NULL;
    for (size_t i = 0; i < q->size; i++) {
        if (q->items[i].score < avg && (!lowest || q->items[i].score < lowest->score)) {
            lowest = &q->items[i];
        }
    }

    if (lowest) {
        queue_push(q, -1, avg);
        lowest->score = avg;
    }
}

int main(void) {
    TaskQueue q;
    queue_init(&q);

    queue_push(&q, 1, 10.0);
    queue_push(&q, 2, 20.0);
    queue_push(&q, 3, 30.0);
    queue_push(&q, 4, 5.0);

    apply_catchup_bonus(&q);

    for (size_t i = 0; i < q.size; i++) {
        printf("task %d -> %.2f\n", q.items[i].id, q.items[i].score);
    }

    queue_free(&q);
    return 0;
}
