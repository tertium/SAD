# This problem was borrowed from the Otter's examples.
# The text must be processed in the theorem-proving mode.

[an animal] [a wolf] [a fox] [a bird] [a worm] [a snail]
[a plant] [a grain] [x eats/eat y] [x is smaller than y]

Every animal A that does not eat some plant eats
(every animal that eats some plant and is smaller than A).

Every wolf is an animal.  Every fox is an animal.
Every bird is an animal.  Every worm is an animal.
Every snail is an animal.  Every grain is a plant.

There exist a wolf and a fox and a bird
        and a worm and a snail and a grain.

Every worm is smaller than every bird.
Every snail is smaller than every bird.
Every bird is smaller than every fox.
Every fox is smaller than every wolf.

Every worm eats some grain.  Every snail eats some grain.
Every bird eats every worm.  Every bird eats no snail.
Every wolf eats no grain.    Every wolf eats no fox.

Proposition.
There exists an animal A and an animal B
such that A eats B and B eats every grain.
