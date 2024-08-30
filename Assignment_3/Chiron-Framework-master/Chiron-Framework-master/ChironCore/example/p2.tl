pendown
	if (:x > :y) [
		forward 80
	if (:z >= :y) [
        left 20
		forward 30]
	else[
		right 20
		forward 30]]
	else [
		backward 80
		if (:z >= :y) [
		left 20	
        forward 50]
	else[ right 20
		forward 50]]