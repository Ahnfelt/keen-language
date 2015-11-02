# Keen
A programming language

# Copy & paste some test code here

    Boolean := [True, False]
    Person := [Person(name : String, age : Int)]
    List<A> := [Empty, Link(head : A, tail : List<A>)]
    Option<A> := [None, Some(value : A)]

    numbers := Link(head = 1, tail = Link(head = 2, tail = Empty))
    add := {|x, y| x + y}
    fac : Int -> Int = {
        |1| 1
        |i| i * fac(i - 1)
    }
    switch := {|value| {|cases| cases(value)}}

    if := {|condition| {|then| {|else| switch(condition) {
        |True| then()
        |False| else()
    }}}}

    when := {|condition| {|body| if(condition)(body){} }}
    unless := {|condition| {|body| if(condition){}(body) }}

    abs := {|x, y|
        if(x > y) {
            x - y
        } {
            y - x
        }
    }
    each := {|list| {|body| switch(list) {
        |Link l|
            body(l.head)
            each(l.tail)(body)
        |Empty|
    }}}
    each(numbers) {|i|
        window.console.log(i)
    }

    Link xs := numbers
    window.console.log(xs.head)
