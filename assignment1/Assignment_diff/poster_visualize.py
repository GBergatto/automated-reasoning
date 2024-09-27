import matplotlib.pyplot as plt
import matplotlib.patches as patches
import random

def random_color():
    """Generate a random color in hex format."""
    return "#{:06x}".format(random.randint(0, 0xFFFFFF))

def draw_layout():
    # Taking layout dimensions
    layout_width = 30.0
    layout_height = 30.0

    # Creating figure and axis for the layout
    fig, ax = plt.subplots()
    ax.set_xlim(0, layout_width)
    ax.set_ylim(0, layout_height)

    # Drawing the layout (as a rectangle)
    layout_rect = patches.Rectangle((0, 0), layout_width, layout_height, linewidth=2, edgecolor='black', facecolor='none')
    ax.add_patch(layout_rect)

    # Number of posters and their dimensions and positions
    num_posters = 11
    posters = [[4,5,5,10],[4,6,9,9],[5,21,0,9],[6,9,13,0],[8,6,5,15],[6,10,13,9],[6,11,13,19],[12,7,1,1],[8,9,5,21],[11,10,19,0],[10,20,20,10],]

    # Loop through the posters, take their dimensions and positions
    for i in range(num_posters):
        poster_width = posters[i][0]
        poster_height = posters[i][1]
        poster_x = posters[i][2]
        poster_y = posters[i][3]

        # Random color
        poster_color = random_color()

        # Drawing the poster
        poster_rect = patches.Rectangle((poster_x, poster_y), poster_width, poster_height, linewidth=1, edgecolor='black', facecolor=poster_color)
        ax.add_patch(poster_rect)

        # Calculate the center of the poster to place the label
        center_x = poster_x + poster_width / 2
        center_y = poster_y + poster_height / 2

        # Add the poster number at the center
        ax.text(center_x, center_y, f'Poster {i+1}', color='black', ha='center', va='center', fontdict=dict({"size": 5.5,"weight":"bold"}))

        # Add edge lengths for the poster, but keep them inside the poster
        offset = 0.2  # Small offset to move text inside the poster

        # Top edge length (just inside the poster)
        ax.text(center_x, poster_y + poster_height - offset, f'{poster_width}', color='black', fontsize=8, ha='center', va='top',fontdict=dict({"style":"italic"}))

        # Bottom edge length (just inside the poster)
        ax.text(center_x, poster_y + offset, f'{poster_width}', color='black', fontsize=8, ha='center', va='bottom',fontdict=dict({"style":"italic"}))

        # Left edge length (just inside the poster, rotated)
        ax.text(poster_x + offset, center_y, f'{poster_height}', color='black', fontsize=8, ha='left', va='center', rotation=90,fontdict=dict({"style":"italic"}))

        # Right edge length (just inside the poster, rotated)
        ax.text(poster_x + poster_width - offset, center_y, f'{poster_height}', color='black', fontsize=8, ha='right', va='center', rotation=90,fontdict=dict({"style":"italic"}))
    
    # Drawing a line
    x_start = 13
    y_start = 0
    x_end = 13
    y_end = 30

    # Drawing the line
    ax.plot([x_start, x_end], [y_start, y_end], color='blue', linewidth=2)

    # Calculate the center point of the line to place the label
    line_center_x = (x_start + x_end) / 2
    line_center_y = (y_start + y_end) / 2

    # Add the line name at the center of the line
    ax.text(line_center_x, line_center_y, "Line", color='darkblue', fontsize=10, ha='center', va='center', backgroundcolor='white')
    
    # Display the layout with posters and line
    plt.gca().set_aspect('equal', adjustable='box')
    plt.title("Layout with Posters")
    plt.xlabel("Width")
    plt.ylabel("Height")
    plt.show()

# Running the function to draw the layout
draw_layout()
