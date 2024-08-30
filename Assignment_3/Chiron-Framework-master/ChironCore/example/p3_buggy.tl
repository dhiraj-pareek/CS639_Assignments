penup

if :x > 0 [
    if :y > 0 [
        if :z > 0 [
            forward 10
            left 45] 
        else [
            forward 10
            right 45]] 
    else [
        if :z > 0 [
            forward 10
            left 30] 
        else [
            forward 100
            right 30]]] 
else [
    if :y > 0 [
        if :z > 0 [
            backward 10
            left 45] 
        else [
            backward 10
            right 45]] 
    else [
        if :z > 0 [
            backward 10
            left 30] 
        else [
            backward 10
            right 30]]]