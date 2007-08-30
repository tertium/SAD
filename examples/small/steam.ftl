[animal/animals] [plant/plants] [eats/eat]

Signature Animal.   An animal is a notion.
Signature Plant.    A plant is a notion.

Let A,B denote animals. Let P denote a plant.

Signature EatAnimal.    A eats B is an atom.
Signature EatPlant.     A eats P is an atom.
Signature Smaller.      A is smaller than B is an atom.

Axiom CruelWorld.   Let B be smaller than A and eat some plant.
                    Then A eats all plants or A eats B.

Signature Wolf.     A wolf is an animal.
Signature Fox.      A fox is an animal smaller than any wolf.
Signature Bird.     A bird is an animal smaller than any fox.
Signature Worm.     A worm is an animal smaller than any bird.
Signature Snail.    A snail is an animal smaller than any bird.
Signature Grain.    A grain is a plant.

Axiom Everybody.    There exist a wolf and a fox and a bird
                        and a worm and a snail and a grain.

Axiom WormGrain.    Every worm eats some grain.
Axiom SnailGrain.   Every snail eats some grain.
Axiom BirdWorm.     Every bird eats every worm.
Axiom BirdSnail.    Every bird eats no snail.
Axiom WolfGrain.    Every wolf eats no grain.
Axiom WolfFox.      Every wolf eats no fox.

Proposition.        There exist animals A,B such that
                    A eats B and B eats every grain.
