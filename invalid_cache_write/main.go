package main

type Cache interface {
	Get(key string, cb func(int, bool))
	Set(key string, value int, cb func(error))
}

type Database interface {
	GetValue(cb func(int, error))
	Write(v int, cb func(error))
}

type app struct {
	cache Cache
	db    Database
}

func newApp(cache Cache, db Database) *app {
	return &app{
		cache: cache,
		db:    db,
	}
}

func (app *app) getValue(reply func(int, error)) {
	var writeToCache = func(value int, err error) {
		if err != nil {
			// TODO
		}

		// Value not set.
		if value == 0 {
			reply(value, nil)
			return
		}

		app.cache.Set("value", value, func(err error) {

			reply(value, err)
		})
	}

	app.cache.Get("value", func(value int, ok bool) {
		if ok {
			reply(value, nil)
			return
		}

		app.db.GetValue(writeToCache)
	})

}

func (app *app) write(v int, reply func(error)) {
	app.db.Write(v, reply)
}

func main() {

}
