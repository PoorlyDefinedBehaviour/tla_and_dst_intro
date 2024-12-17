package main

import (
	"fmt"
	"math/rand"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

const (
	OpGetValue    = "getValue"
	OpSetValue    = "setValue"
	OpTickCache   = "tickCache"
	OpExpireCache = "expireCache"
	OpTickDb      = "tickDb"
)

func TestApp(t *testing.T) {
	t.Parallel()

	seed := time.Now().UnixMicro()
	fmt.Printf("SEED=%d\n", seed)
	rng := rand.New(rand.NewSource(seed))

	oracle := newOracle(t)
	cache := newMockCache(rng, oracle)
	db := newMockDatabase()
	app := newApp(cache, db)

	for i := 0; i < 200; i++ {
		actions := enabledActions(db, cache)
		action := choose(rng, actions)

		switch action {
		case OpGetValue:
			app.getValue(func(i int, err error) {

			})

		case OpSetValue:
			app.write(i, func(err error) {

			})

		case OpTickCache:
			cache.tick()

		case OpExpireCache:
			// cache.expire()

		case OpTickDb:
			db.tick()
		}

	}
}

func enabledActions(db *mockDatabase, cache *mockCache) []string {
	actions := []string{OpGetValue, OpSetValue}
	if len(db.queue) > 0 {
		actions = append(actions, OpTickDb)
	}
	if len(cache.queue) > 0 {
		actions = append(actions, OpTickCache)
	}
	if cache.value != 0 {
		actions = append(actions, OpExpireCache)
	}
	return actions
}

func choose[T any](rng *rand.Rand, xs []T) T {
	i := rng.Intn(len(xs))
	return xs[i]
}

const (
	cacheMsgTypeGet = "get"
	cacheMsgTypeSet = "set"
)

type pendingCacheOperation struct {
	// Required.
	typ string
	// Required for: Get
	replyGet func(int, bool)
	// Required for: Set
	replySet func(error)
	// Required for: Get, Set
	key string
	// Required for: Set
	value int
}

type mockCache struct {
	queue  []pendingCacheOperation
	rng    *rand.Rand
	oracle *oracle
	value  int
}

func newMockCache(rng *rand.Rand, oracle *oracle) *mockCache {
	return &mockCache{rng: rng, oracle: oracle}
}

func (cache *mockCache) Get(key string, cb func(int, bool)) {
	cache.queue = append(cache.queue, pendingCacheOperation{
		typ:      cacheMsgTypeGet,
		key:      key,
		replyGet: cb,
	})
}

func (cache *mockCache) Set(key string, value int, cb func(error)) {
	fmt.Printf("\n\naaaaaaa CACHE queued SET %+v\n\n", value)
	cache.queue = append(cache.queue, pendingCacheOperation{
		typ:      cacheMsgTypeSet,
		key:      key,
		value:    value,
		replySet: cb,
	})
}

func (cache *mockCache) expire() {
	cache.value = 0
}

func (cache *mockCache) tick() {
	if len(cache.queue) == 0 {
		return
	}

	i := cache.rng.Intn(len(cache.queue))
	msg := cache.queue[i]
	cache.queue = append(cache.queue[:i], cache.queue[i+1:]...)

	switch msg.typ {
	case cacheMsgTypeGet:
		msg.replyGet(cache.value, cache.value != 0)

	case cacheMsgTypeSet:
		cache.value = msg.value
		cache.oracle.onCacheSet(msg.key, msg.value)

	default:
		panic(fmt.Sprintf("cache: unknown message type: %+v", msg.typ))
	}
}

const (
	dbMsgTypeGetValue = "GetValue"
	dbMsgTypeWrite    = "Write"
)

type pendingDbOperation struct {
	// Required.
	typ string
	// Required for: GetValue
	replyGetValue func(int, error)
	// Required for: Write
	replyWrite func(error)
	// Required for: Write
	value int
}

type mockDatabase struct {
	queue []pendingDbOperation
	value int
}

func newMockDatabase() *mockDatabase {
	return &mockDatabase{

		value: 0,
	}
}

func (db *mockDatabase) GetValue(cb func(int, error)) {
	db.queue = append(db.queue, pendingDbOperation{
		typ:           dbMsgTypeGetValue,
		replyGetValue: cb,
	})
}

func (db *mockDatabase) Write(value int, cb func(error)) {
	db.queue = append(db.queue, pendingDbOperation{
		typ:        dbMsgTypeWrite,
		replyWrite: cb,
		value:      value,
	})
}

func (db *mockDatabase) tick() {
	if len(db.queue) == 0 {
		return
	}

	msg := db.queue[0]
	db.queue = db.queue[1:]

	switch msg.typ {
	case dbMsgTypeGetValue:
		msg.replyGetValue(db.value, nil)
	case dbMsgTypeWrite:
		db.value = msg.value
		msg.replyWrite(nil)
	default:
		panic(fmt.Sprintf("cache: unknown message type: %+v", msg.typ))
	}
}

type oracle struct {
	t     *testing.T
	key   string
	value int
}

func newOracle(t *testing.T) *oracle {
	return &oracle{t: t}
}

func (o *oracle) onCacheSet(key string, value int) {
	if o.key != "" {
		assert.Equal(o.t, o.key, key)
	}

	fmt.Printf("\n\naaaaaaa ORACLE onCacheSet: oldValue %+v newValue %+v\n\n", o.value, value)
	require.LessOrEqual(o.t, o.value, value)

	o.value = value
}
