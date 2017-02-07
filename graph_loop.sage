"""
Code to draw loops as directed arrows in directed graph plots.

This is fairly hacky and brittle, because it hijacks an internal function in
GraphPlot and replaces the loops with different graphics.
"""
from sage.graphs.graph_plot import GraphPlot
from sage.plot.circle import Circle
from sage.plot.all import arrow

if not hasattr(GraphPlot, 'real_set_edges'):
    GraphPlot.real_set_edges = GraphPlot.set_edges

def determine_path(x, y, r, graph, pos):
    graph = graph.to_undirected()
    for v in graph.vertex_iterator():
        if pos[v][0] == x and pos[v][1] == y + r:
            break
    N = graph.neighbors(v)
    Npos = [pos[n] for n in N]

    def above((nx, ny)):
        return ny > y
    def below((nx, ny)):
        return ny < y
    def rightof((nx, ny)):
        return nx > x
    def leftof((nx, ny)):
        return nx < x

    a = len(filter(above, Npos))
    b = len(filter(below, Npos))
    lo = len(filter(leftof, Npos))
    ro = len(filter(rightof, Npos))

    m = min(a,b,lo,ro)
    r = r*0.8
    if m == a:
        start = (x - r/sqrt(2), y + r/sqrt(2))
        midl = (x - 2*r/sqrt(2), y + 3*r)
        midr = (x + 2*r/sqrt(2), y + 3*r)
        end = (x + r/sqrt(2), y + r/sqrt(2))
    elif m == b:
        start = (x - r/sqrt(2), y - r/sqrt(2))
        midl = (x - 2*r/sqrt(2), y - 3*r)
        midr = (x + 2*r/sqrt(2), y - 3*r)
        end = (x + r/sqrt(2), y - r/sqrt(2))
    elif m == ro:
        start = (y - r/sqrt(2), x + r/sqrt(2))[::-1]
        midl = (y - 2*r/sqrt(2), x + 3*r)[::-1]
        midr = (y + 2*r/sqrt(2), x + 3*r)[::-1]
        end = (y + r/sqrt(2), x + r/sqrt(2))[::-1]
    else:
        start = (y - r/sqrt(2), x - r/sqrt(2))[::-1]
        midl = (y - 2*r/sqrt(2), x - 3*r)[::-1]
        midr = (y + 2*r/sqrt(2), x - 3*r)[::-1]
        end = (y + r/sqrt(2), x - r/sqrt(2))[::-1]

    return [[start, midl, midr, end]]

def my_set_edges(self, **edge_options):
    """
    Modified GraphPlot.set_edges function to make loops be directed
    arrows instead of circles.
    """
    GraphPlot.real_set_edges(self, **edge_options)
    if not self._graph.is_directed():
        return
    new_edge_components = []
    for e in self._plot_components['edges']:
        o = e._objects[0]
        if not isinstance(o, Circle):
            new_edge_components.append(e)
        else:
            x, y, r = o.x, o.y, o.r
            path = determine_path(x, y+r, r, self._graph, self._pos)

            # Handle base edge options: thickness, linestyle
            eoptions={}
            if 'edge_style' in self._options:
                eoptions['linestyle'] = self._options['edge_style']
            if 'thickness' in self._options:
                eoptions['thickness'] = self._options['thickness']
            eoptions["color"] = o._options["rgbcolor"]

            a = arrow(path=path, **eoptions)
            new_edge_components.append(a)
    self._plot_components['edges'] = new_edge_components

GraphPlot.set_edges = my_set_edges
