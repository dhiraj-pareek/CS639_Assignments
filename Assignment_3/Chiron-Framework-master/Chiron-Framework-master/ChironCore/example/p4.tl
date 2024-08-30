penup
if :x > 0 [
    if :y > 0 [
        if :z > 0 [
            forward 50]
        else [
            left 45
            forward 40]]
    else [
        if :z > 0 [
            right 45
            backward 50]
        else [
            forward 10]]]
else [
    if :y > 0 [
        if :z > 0 [
            left 45
            forward 50] 
        else [
            forward 30]]
     else [
        if :z > 0 [
            right 45
            backward 40] 
            else [
            backward 50]]]
