if (:x > :y) [
    left 45
    forward 70
    if (:z >= :a) [
            left 45
            forward 50
        if (:a < :x) [
            left 45
            forward 50
                    
        ] else [
            left 45
            backward 70
        ]
    ] else [
        right 45
        forward 50
        if (:a < :y) [
            left 45
            forward 50
            
        ] else [
            left 45
            backward 70
        ]
    
]] else [
    left 45
    backward 70
    if (:z >= :a) [
            right 45
            backward 50
        if (:y < :z) [
            left 45
            forward 50
        ] else [ 
            right 45
            backward 50
        ]
    ] else [
        left 45
        forward 70
        if (:a < :y) [
            right 45
            forward 50
        ] else [
            left 45
            backward 50
        ]
    ]
]
