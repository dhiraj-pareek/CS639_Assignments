if (:x > :y ) [

        if (:x > :z ) [
    
    if (:z >= :a) [
        repeat 4 [
            backward 30
            right 90
        ]
    ] else [
        repeat 3 [
            backward 40
            left 120
        ]
    ]
] else [
    if (:z > :a) [
        repeat 5 [
            backward 50
            left 72
        ]
    ] else [
        repeat 6 [
            backward 45
            right 60
        ]
    ]
  ]
]
 else [
        if (:x > :z ) [
    
    if (:z >= :a) [
        repeat 4 [
            forward 30
            right 90
        ]
    ] else [
        repeat 3 [
            forward 40
            left 120
        ]
    ]
] else [
    if (:z > :a) [
        repeat 5 [
            forward 50
            left 72
        ]
    ] else [
        repeat 6 [
            forward 45
            right 60
        ]
    ]
]]






