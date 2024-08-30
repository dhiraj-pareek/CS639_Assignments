if (:x > :y) [
    forward 60
    if (:z >= :a) [
        left 60
        forward 50
        if (:x > :z) [
            left 60
            forward 50
        ] else [
            right 60
            forward 50  
        ]
    ] else [
        right 60
        forward 50
        if (:a > :y) [
            left 60
            forward 50
        ] else [
            right 60
            forward 50 
            ]]
] else [
    backward 60
    if (:z >= :a) [
        right 60
        backward 50
        if (:x > :a) [
            right 60
        backward 50
        ] else [
            left 60
        backward 50
            ]
    ] else [
        left 60
        backward 50
        if (:x > :z) [
            right 60
        backward 50
            
        ] else [
            left 60
        backward 50
            ]]]
