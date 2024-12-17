package main

func writeToDb() error {
	return nil
}

func writeToK8s() error {
	return nil
}

func main() {
	// Inside of a transaction...
	if err := writeToDb(); err != nil {
		// rollback
	}

	if err := writeToK8s(); err != nil {
		// rollback
	}

	// commit
}
