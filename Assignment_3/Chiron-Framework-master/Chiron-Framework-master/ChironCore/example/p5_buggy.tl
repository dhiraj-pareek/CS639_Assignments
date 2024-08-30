penup
if :x > 0 [
    if :y > 0 [
        if :z > 0 [
            forward 50
            left 45] 
        else [
            forward 50
            right 45]] 
    else [
        if :z > 0 [
            left 30
            forward 50]
        else [
            right 30
            forward 80]]] 
else [
    if :y > 0 [
        if :z > 0 [
            forward 30
            left 45]
        else [
            forward 30
            right 45]]
    else [
        if :z > 0 [
            left 30
            forward 40]
        else [
            right 30
            forward 60]]]