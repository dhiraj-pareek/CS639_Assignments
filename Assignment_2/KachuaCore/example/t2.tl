if (:x > :y ) [
    if (:z >= :a) [
        repeat 4 [
            forward 40
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
]