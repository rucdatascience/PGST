# Approximating Probabilistic Group Steiner Trees in Graphs

The introduction of these files are as follows. 


# Datasets

<b>The Amazon dataset</b> is in the amazon folder. The dictionary is as follows.

Each column of "amazon_items.txt" contains the information of an item: "Item_ID, Average_rating_of_this_item, Keywords_of_this_item". For example, "\<itemid\>3\<itemid\/>\<avg_rating\>5\<avg_rating\/>\<keywords\>100000009,100000010\<keywords\/>" means that Item 3 has an average rating of 5, and the keywords associated with Item 3 are 100000009 and 100000010. There are 548552 items in total.

Each column of "amazon_keywords.txt" corresponds to a keyword, and contain the ID of a keyword and the name of this keyword. For example, "100000417	Sheldon, Jack" means that the keyword of "Sheldon, Jack" has an ID of 100000417. There are 25958 keywords in total.

Each column of "amazon_items_links.txt" contains the IDs of two items, and indicates that there are users who bought these two items at the Amazon website at the same time. We link such a pair of items. There are 987942 links in total.



<b>The DBLP dataset</b> is in the dblp folder. The dictionary is as follows.

Each Line of "dblp_v12_fields.txt" corresponds to a field of study. For example, "880<&>Second-language attrition" means that the field of "Second-language attrition" has a field ID of 880. There are 132337 fields of study in total.

Each line of "dblp_v12_papers.txt" corresponds to a paper, and contain the 
following information:"Paper_ID<&>Paper_title<&>Fields_of_study_IDs_and_Weights". For example, "5<&>Vectorial fast correlation attacks.<&><30,0.3682>;<1,0.416>;<18,0>;<31,0.6393>" means that Paper 5 has the title of “Vectorial fast correlation attacks.”, and are in the fields of 30, 1, 18, 31. This paper is associated with the weights of 0.3682, 0.416, 0, 0.6393 for the above fields (large weights indicate
high probabilities). 

Each line of "dblp_v12_linkes.txt" contains the IDs of two papers, and shows that the first paper cites the second paper.



<b>The Movie dataset</b> is in the movie folder. The dictionary is as follows.

Each line of "MovieLens_25M_movie_info.txt" corresponds to the information of a movie: Movie_ID(start from 0):::Movie_name:::Average_star:::genres. For example, "5:::Homage (1995):::2.536:::6_Drama", which means that Movie 5 has a name of Homage (1995), and has an average rating star of 2.536, and the genre of this movie is Drama (the genre ID of Drama is 6). There are 62423 movies in total.

Each line of "MovieLens_25M_movie_links.txt" contains a pair of movies such that there are users who rate both these two movies five stars. The content in each line is "Movie_ID1(start from 0):::Movie_ID2(start from 0):::Number_of_common_5_star_raters". For example, "1252:::1395:::79" means that there are users who rate five stars to both Movies 1252 and 1395, and the number of such persons is 79. There are 35323774 pairs of movie in total.




# C++ codes 

The C++ source codes are in <b>PGST.cpp</b>. 

It is recommended to fold all the regions of codes for easy reading (by pressing Ctrl+M+O in Visual Studio). 

Running these codes requires some header files (e.g. #include <graph_hash_of_mixed_weighted/graph_hash_of_mixed_weighted.h>; see cppheader_202*****.zip) and the Boost library: https://www.boost.org/ (e.g. #include <boost/random.hpp>) . 

We use the above datasets to generate binary graph files for the experiments. The reason for generating binary files is that it is much faster to read binary files than to read raw data files. We use the function "produce_binary_graph_files_for_experiments" in the codes to generate all binary graph files for the experiments in our paper. For example, the binary file "amazon_read_graph_one_edge_weight_548552.bin" is generated by the above function, and records the full amazon graph where all edge costs are 1.

After generating binary graph files, we use the function "generate_binary_PLL_indexes" to generate hub labels that record shortest paths in graphs. For example, the label file "PLL_binary_amazon_one_edge_weight_548552.txt" is generated by the above function, and records the shortest paths in the full amazon graph where all edge costs are 1. Notably, each label file for a DBLP graph consumes dozens of GB memory and storage. So, make sure there is enough space for generating and saving these files. These labels are required for our experiments. 

After making the header files; binary graph files; and hub labels ready, <b>all the experiments in our paper can be conducted by running the function "experiments()"</b>, Make sure there is enough memory (at least 300 GB memory for hub labels and other consumption).

To read these C++ codes in detail, it is recommended to start from "experiments()", and then go to "experiment_element". More detailed codes in other regions can then be traced, such as the codes of proposed three algorithms below "/*proposed algorithms*/"


