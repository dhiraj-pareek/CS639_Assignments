penup
if :x>:y [
    if :y>20 [
        forward 50]
    else [
        left 45
        backward 20]]
else [
    if :y>20 [
        right 45
        forward 10]
    else [
        forward 30]]