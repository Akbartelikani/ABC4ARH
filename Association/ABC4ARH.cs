using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Windows.Forms;
using System.Xml.Serialization;
using System.IO;
using System.Collections;
using System.Xml;
using System.Diagnostics;

namespace Association
{
    public partial class ABC4ARH : Form
    {
        //==============================================================
        //          Control Parameters of ABC algorithm
        //==============================================================
        int NP=10000; /* The number of colony size (employed bees+onlooker bees)*/
        int FoodNumber=5000; /*The number of food sources equals the half of the colony size*/
        int limit=100;  /*A food source which could not be improved through "limit" trials is abandoned by its employed bee*/
        int maxCycle=3000; /*The number of cycles for foraging {a stopping criteria}*/
        //==============================================================
        //          Problem specific variables and arrays for ABC
        //==============================================================
        int D = 1000; /*The number of parameters of the problem to be optimized*/
        double lb = -5.12; /*lower bound of the parameters. */
        double ub = 5.12; /*upper bound of the parameters. lb and ub can be defined as arrays for the problems of which parameters have different bounds*/
        int runtime = 30;  /*Algorithm can be run many times in order to see its robustness*/
        int[] similarity_vector = new int[10000];
        double[] solution = new double[10000]; /*New solution (neighbour) produced by v_{ij}=x_{ij}+\phi_{ij}*(x_{kj}-x_{ij}) j is a randomly chosen parameter and k is a randomlu chosen solution different from i*/
        double[,] Population = new double[5000, 10000]; /*Foods is the population of food sources. Each row of Foods matrix is a vector holding D parameters to be optimized. The number of rows of Foods matrix equals to the FoodNumber*/
        double[] Fitness_values = new double[5000];/*f is a vector holding objective function values associated with food sources */
        double[] trial = new double[5000]; /*trial is a vector holding trial numbers through which solutions can not be improved*/
        double[] prob = new double[5000]; /*prob is a vector holding probabilities of food sources (solutions) to be chosen*/
        double ObjValSol; /*Objective function value of new solution*/
        double FitnessSol; /*Fitness value of new solution*/
        double[] f = new double[5000]; /*fitness is a vector holding fitness (quality) values associated with food sources*/
        int neighbour1, neighbour2, param2change; /*param2change corrresponds to j, neighbour corresponds to k in equation v_{ij}=x_{ij}+\phi_{ij}*(x_{kj}-x_{ij})*/
        double GlobalMin; /*Optimum solution obtained by ABC algorithm*/
        double[] GlobalParams = new double[5000]; /*Parameters of the optimum solution*/
        double[] GlobalMins = new double[10]; /*GlobalMins holds the GlobalMin of each run in multiple runs*/
        double r; /*a random number in the range [0,1)*/
        //==============================================================
        //          Variables for similarity
        //==============================================================
        int M11 = 0, M10 = 0, M01 = 0;
        int n1 = 0, n0 = 0;
        Single min_supp;
        int MSTint = 0;
        double Dissimilarity = 0, Dissimilarity_new=0;
        int M11_new = 0, M01_new = 0, M10_new = 0;
        int[] bits = new int[3];
        //==============================================================
        //          Variables for side effects
        //==============================================================
        double[,] PopEffects = new double[10000,3];//Stores 3 side-effects of solutions
        double HF_sol, LR_sol, NR_sol = 0; 
        double minimum_dis = 0;
        //==============================================================
        //          Problem specific variables and arrays for program
        //==============================================================
        double ConfCurrent = 0;
        int[,] trans_length = new int[100000, 2];
        int[] trans_vector = new int[10000];
        int[,] trans_index = new int[5000,5000];
        int[,] LeftTrans = new int[5000, 5000];
        int[,] right_support = new int[200, 2];//items and their support
        int[] corressponding_index = new int[100000];
        string[] input_items = new string[20000];
        int trans_count = 0;
        private string strfilename1;
        int end = 0;
        int items_number = 0;
        int[,] length = new int[2,10000];
        int trans_number = 0;
        Single rnd_ut;
        string[,] input_file = new string[10000, 300];//**Array of dataset
        string[,] temp_input = new string[10000, 300];
        string[,] itemsets = new string[5000, 100];//**Array of itemsets
        int[] support = new int[5000];//**Array of support of itemsets
        int[,] index_fi = new int[200, 3];
        int rule_index = 0;// is used for strong rules
        double[] confidence = new double[200000];//**Array of the confidence of rules
        string[,] left = new string[10000, 50];//**Array of the LHS itemsets
        string[,] right = new string[10000, 50];//**Array of the RHS itemsets
        int k = 1;
        int intrnd;
        int intrnd_pi;
        int sensitive_count;
        int[] index_sensitive = new int[10000];
        int max_sanitization = 0;

        public ABC4ARH()
        {
            InitializeComponent();
        }

        private void button16_Click(object sender, EventArgs e)
        {
            double NR;
            double LR;
            double ACC1;
            double ACC2;
            double data_utility;
            min_supp = Convert.ToSingle(textBox43.Text.Trim());
            MSTint=Convert.ToInt32(min_supp*Convert.ToSingle(trans_number));
            
            /*Main program of the ABC algorithm*/
            int iter, run, j;
            double mean;
            mean = 0;
            for (run = 0; run < runtime; run++)
            {
                initial();
                MemorizeBestSource();
                for (iter = 0; iter < maxCycle; iter++)
                {
                    SendEmployedBees();
                    CalculateProbabilities();
                    SendOnlookerBees();
                    MemorizeBestSource();
                    SendScoutBees();
                }
                GlobalMins[run] = GlobalMin;
                mean = mean + GlobalMin;
            }
            mean = mean / runtime;
        }

        private void button4_Click(object sender, EventArgs e)
        {
            int k_file = 1;
            //////////////////////
            int fi_number = 0;
            openFileDialog2.Filter = "Text Files (*.txt) | *.txt|" + "CSV Files (*.csv) | *.csv|" + "All Files (*.*)| *.*";
            openFileDialog2.FilterIndex = 1;
            openFileDialog2.Title = "انتخاب مجموعه فقره های تکرارشونده";
            if (openFileDialog2.ShowDialog() == DialogResult.OK)
            {
                strfilename1 = openFileDialog2.FileName;
                StreamReader sd = new StreamReader(strfilename1);
                while (sd.EndOfStream == false)
                {
                    string nextline = sd.ReadLine();
                    string[] strword = nextline.Split(',');
                    k_file = strword.Length;
                    for (int i = 0; i < strword.Length; i++)
                        itemsets[fi_number, i] = strword[i];
                    index_fi[strword.Length - 1, 2] = fi_number;
                    fi_number++;
                    k = k_file;
                    end = fi_number;
                }
                index_fi[0, 0] = 1;
                index_fi[0, 1] = 0;
                for (int i = 1; i < k; i++)
                {
                    index_fi[i, 0] = i + 1;
                    index_fi[i, 1] = index_fi[i - 1, 2] + 1;
                }
                txt_count_FI.Text = fi_number.ToString();
                button9.Enabled = true;
            }
        }

        private void button9_Click(object sender, EventArgs e)
        {
            openFileDialog2.Filter = "Text Files (*.txt) | *.txt|" + "CSV Files (*.csv) | *.csv|" + "All Files (*.*)| *.*";
            openFileDialog2.FilterIndex = 1;
            openFileDialog2.Title = "انتخاب فایل پشتیبانی برای فقره های تکرارشونده";
            if (openFileDialog2.ShowDialog() == DialogResult.OK)
            {
                strfilename1 = openFileDialog2.FileName;
                StreamReader sd = new StreamReader(strfilename1);
                int supp_index = 0;
                while (sd.EndOfStream == false)
                {
                    string nextline = sd.ReadLine();
                    support[supp_index] = Convert.ToInt32(nextline);
                    supp_index++;
                }
                end = supp_index;
                txt_count_FI.Text = end.ToString();
                button2.Enabled = true;
            }
        }

        private void button2_Click(object sender, EventArgs e)
        {
            openFileDialog2.Filter = "Text Files (*.txt) | *.txt|" + "CSV Files (*.csv) | *.csv|" + "All Files (*.*)| *.*";
            openFileDialog2.FilterIndex = 1;
            openFileDialog2.Title = "انتخاب فایل پشتیبانی برای فقره های تکرارشونده";
            if (openFileDialog2.ShowDialog() == DialogResult.OK)
            {
                int ar_row_index = 0;
                strfilename1 = openFileDialog2.FileName;
                StreamReader sd = new StreamReader(strfilename1);
                while (sd.EndOfStream == false)
                {
                    string nextline = sd.ReadLine();
                    string[] strword = nextline.Split('>');
                    string[] str_left = strword[0].Split(',');

                    for (int i = 0; i < str_left.Length; i++)
                        left[ar_row_index, i] = str_left[i];

                    string[] str_right = strword[1].Split(',');
                    for (int i = 0; i < str_right.Length; i++)
                        right[ar_row_index, i] = str_right[i];

                    ar_row_index++;
                }
                rule_index = ar_row_index;
                txt_count_ARs.Text = rule_index.ToString();
                button1.Enabled = true;
            }
        }

        private void button1_Click(object sender, EventArgs e)
        {
            openFileDialog2.Filter = "Text Files (*.txt) | *.txt|" + "CSV Files (*.csv) | *.csv|" + "All Files (*.*)| *.*";
            openFileDialog2.FilterIndex = 1;
            openFileDialog2.Title = "انتخاب فایل پشتیبانی برای فقره های تکرارشونده";
            if (openFileDialog2.ShowDialog() == DialogResult.OK)
            {
                strfilename1 = openFileDialog2.FileName;
                StreamReader sd = new StreamReader(strfilename1);
                int conf_index = 0;
                while (sd.EndOfStream == false)
                {
                    string nextline = sd.ReadLine();
                    confidence[conf_index] = Convert.ToDouble(nextline);
                    conf_index++;
                }
                rule_index = conf_index;
            }
        }
//==============================================================
//     Calculates Fitness function
//==============================================================
double CalculateFitness(int index)
{
    double result = 0;
    int rStateSupp = 0;
    int HidingFailure = 0;
    for (int i = 0; i < sensitive_count; i++)
    {
        int next1 = 0, next2 = 0, rule_ln = 0, SuppCurrent = 0;
        string[] temp = new string[30];

        while (left[index_sensitive[i], next1] != null)
        {
            temp[next1] = left[index_sensitive[i], next1];
            next1++;
        }
        while (right[index_sensitive[i], next2] != null)
        {
            temp[next1 + next2] = right[index_sensitive[i], next2];
            next2++;
        }
        rule_ln = next1 + next2;
        SuppCurrent = FindSupport(rule_ln, temp);
        int col = 0;
        while (trans_index[i, col] != 0)
        {
            int col1 = 0;
            while (trans_vector[col1] != trans_index[i, col])
                col1++;
            if (Population[index, col1] == 1)
                SuppCurrent--;
        }
        if (SuppCurrent > MSTint)
            HidingFailure++;
    }
    return result;
}
//==============================================================
//     Finds the corresponding transactions and Generates vector
//==============================================================
int FindTrans()
{
    int result = 0;
    for (int i = 0; i < sensitive_count; i++)
    {
        int next1 = 0;
        int next2 = 0;
        int rule_ln = 0;
        string[] temp = new string[30];
        string[] TempLeft = new string[10];
        string[] Tempright = new string[10];
        while (left[index_sensitive[i], next1] != null)
        {
            temp[next1] = left[index_sensitive[i], next1];
            TempLeft[next1] = temp[next1];
            next1++;
        }
        while (right[index_sensitive[i], next2] != null)
        {
            temp[next1 + next2] = right[index_sensitive[i], next2];
            Tempright[next2] = temp[next1 + next2];
            next2++;
        }
        rule_ln = next1 + next2;
        int trans_count = 0;
        int trans_count1 = 0;
        for (int x = 0; x < trans_number; x++)
        {
            int count = 0;
            int count_left = 0;
            for (int y = 0; y < rule_ln; y++)
            {
                int column = 0;
                while (input_file[x, column] != null)
                {
                    if (string.Equals(temp[y], input_file[x, column]) == true)
                    {
                        count++;
                        break;
                    }
                    column++;
                }
                int column1 = 0;
                while (input_file[x, column1] != null)
                {
                    if (string.Equals(TempLeft[y], input_file[x, column1]) == true)
                    {
                        count_left++;
                        break;
                    }
                    column1++;
                }
            }
            if (count == rule_ln)
            {
                trans_index[i, trans_count] = x;
                trans_count++;
                ////////**Generate Food vector//////////
                int y = 0;
                bool find = false;
                while (trans_vector[y] != 0)
                {
                    if (x == trans_vector[y])
                    {
                        find = true;
                        break;
                    }
                    y++;
                }
                if (find == false)
                {
                    trans_vector[result] = x;
                    result++;
                }
            }
            if (count_left == next1)
            {
                LeftTrans[i, trans_count1] = x;
                trans_count1++;
            }
        }
    }
    return result;
}
//==============================================================
//     Finds the support of the generating itemset
//==============================================================
int FindSupport(int index1, string[] temp1)
{
    int result = 0;
    for (int j = index_fi[index1, 1]; j <= index_fi[index1, 2]; j++)
    {
        int item_index = 0;
        int count_find = 0;
        while (string.Equals(temp1[item_index], itemsets[j, item_index]) == true)
            count_find++;

        if (count_find == index1)
        {
            result = support[result];
            break;
        }
    }
    return result;
}
//==============================================================
//     
//==============================================================
void CalculateLR()
{
    
}
//==============================================================
//              The best food source is memorized
//==============================================================
void MemorizeBestSource()
{
    int i, j;

    for (i = 0; i < FoodNumber; i++)
    {
        if (f[i] < GlobalMin)
        {
            GlobalMin = f[i];
            for (j = 0; j < D; j++)
                GlobalParams[j] = Population[i, j];
        }
    }
}
//==============================================================
//     Counters of food sources are initialized in this function
//==============================================================
void init(int index)
{
    D = FindTrans();
    for (int i = 0; i < max_sanitization; i++)
    {
        CrtRnd_pi();
        while (Population[index, intrnd_pi] != 0)
            CrtRnd_pi();
        Population[index, intrnd_pi] = 1;
        solution[intrnd_pi] = Population[index, intrnd_pi];
    }
    Fitness_values[index] = CalculateFitness(index);
    trial[index] = 0;
}
//==============================================================
//              All food sources are initialized
//==============================================================
void initial()
{
    for (int i = 0; i < FoodNumber; i++)
        init(i);
    GlobalMin = f[0];
    for (int i = 0; i < D; i++)
        GlobalParams[i] = Population[0, i];
}
//==============================================================
//Computes the maximum number of sanitization for sensitive rules
//==============================================================
int MaxSan()
{
    int result = 0;
    for (int i = 0; i < sensitive_count; i++)
    {
        int next1=0, next2=0, rule_ln=0, SuppCurrent=0;
        string[] temp = new string[30];
        string[] TempLeft = new string[10];
        while (left[index_sensitive[i], next1] != null)
        {
            temp[next1] = left[index_sensitive[i], next1];
            TempLeft[next1] = temp[next1];
            next1++;
        }
        while (right[index_sensitive[i], next2] != null)
        {
            temp[next1 + next2] = right[index_sensitive[i], next2];
            next2++;
        }
        rule_ln = next1 + next2;
        SuppCurrent = FindSupport(rule_ln, temp);
    }
    return result;
}
///////////////////////////////////////////////////////////
void FindItemset(int index)
{

}
//==============================================================
//              
//==============================================================
void SendEmployedBees()
{
    int i, j;
    /*Employed Bee Phase*/
    for (i = 0; i < FoodNumber; i++)
    {
        /*The parameter to be changed is determined randomly*/
        CrtRnd_pi();
        r = Convert.ToSingle(intrnd_pi) / 100;
        param2change = (int)(r * D);

        /*Randomly selected solution must be different from the solution i*/
        while (neighbour1 == i || neighbour2 == i || neighbour1 == neighbour2)
            RandomVectors();

        for (j = 0; j < D; j++)
            solution[j] = Population[i, j];

        for (j = 0; j < D; j++)
        {
            if (Population[neighbour1, j] == 1 && Population[neighbour2, j] == 1)
                similarity_vector[j] = 1;
            else
                similarity_vector[j] = 0;
        }

        Dissimilarity_func(i, similarity_vector);
        Boolean stop = false;
        while (stop == false)
        {
            Calculatebits();
            double close_value = Dissimilarity - Dissimilarity_new;
            if (minimum_dis > close_value)
            {
                minimum_dis = close_value;
                bits[0] = M11_new;
                bits[2] = M01_new;
                bits[3] = M10_new;
            }
        }

        /*v_{ij}=x_{ij}+\phi_{ij}*(x_{kj}-x_{ij}) */
        CrtRnd_pi();
        r = Convert.ToSingle(intrnd_pi) / 100;
        solution[param2change] = Population[i, param2change] + (Population[i, param2change] - Population[neighbour1, param2change]) * (r - 0.5) * 2;

        /*if generated parameter value is out of boundaries, it is shifted onto the boundaries*/
        if (solution[param2change] < lb)
            solution[param2change] = lb;
        if (solution[param2change] > ub)
            solution[param2change] = ub;
        /*ObjValSol = function(solution);
        /*FitnessSol = CalculateFitness(ObjValSol);*/

        /*a greedy selection is applied between the current solution i and its mutant*/
        if (FitnessSol > Fitness_values[i])
        {
            /*If the mutant solution is better than the current solution i, replace the solution with the mutant and reset the trial counter of solution i*/
            trial[i] = 0;
            for (j = 0; j < D; j++)
                Population[i, j] = solution[j];
            f[i] = ObjValSol;
            Fitness_values[i] = FitnessSol;
        }
        else
            /*if the solution i can not be improved, increase its trial counter*/
            trial[i] = trial[i] + 1;
    }
    /*end of employed bee phase*/
}
//==============================================================
// probability values are calculated by using fitness values and 
// normalized by dividing maximum fitness value           
//==============================================================
void CalculateProbabilities()
{
    int i;
    double maxfit;
    maxfit = Fitness_values[0];
    for (i = 1; i < FoodNumber; i++)
    {
        if (Fitness_values[i] > maxfit)
            maxfit = Fitness_values[i];
    }
    for (i = 0; i < FoodNumber; i++)
        prob[i] = (0.9 * (Fitness_values[i] / maxfit)) + 0.1;
}
//==============================================================
//         
//==============================================================
void SendOnlookerBees()
{

    int i, j, t;
    i = 0;
    t = 0;
    /*onlooker Bee Phase*/
    while (t < FoodNumber)
    {
        CrtRnd_pi();
        r = Convert.ToSingle(intrnd_pi) / 100;
        if (r < prob[i]) /*choose a food source depending on its probability to be chosen*/
        {
            t++;

            /*The parameter to be changed is determined randomly*/
            CrtRnd_pi();
            r = Convert.ToSingle(intrnd_pi) / 100;
            param2change = (int)(r * D);

            /*A randomly chosen solution is used in producing a mutant solution of the solution i*/
            CrtRnd_pi();
            neighbour1 = (int)((Convert.ToSingle(intrnd_pi) / 100) * FoodNumber);

            /*Randomly selected solution must be different from the solution i*/
            while (neighbour1 == i)
            {
                CrtRnd_pi();
                r = Convert.ToSingle(intrnd_pi) / 100;
                neighbour1 = (int)(r * FoodNumber);
            }
            for (j = 0; j < D; j++)
                solution[j] = Population[i, j];

            /*v_{ij}=x_{ij}+\phi_{ij}*(x_{kj}-x_{ij}) */
            CrtRnd_pi();
            r = Convert.ToSingle(intrnd_pi) / 100;
            solution[param2change] = Population[i, param2change] + (Population[i, param2change] - Population[neighbour1, param2change]) * (r - 0.5) * 2;

            /*if generated parameter value is out of boundaries, it is shifted onto the boundaries*/
            if (solution[param2change] < lb)
                solution[param2change] = lb;
            if (solution[param2change] > ub)
                solution[param2change] = ub;
            //ObjValSol = function(solution);
            //FitnessSol = CalculateFitness(ObjValSol);

            /*a greedy selection is applied between the current solution i and its mutant*/
            if (FitnessSol > Fitness_values[i])
            {
                /*If the mutant solution is better than the current solution i, replace the solution with the mutant and reset the trial counter of solution i*/
                trial[i] = 0;
                for (j = 0; j < D; j++)
                    Population[i, j] = solution[j];
                f[i] = ObjValSol;
                Fitness_values[i] = FitnessSol;
            }
            else
                /*if the solution i can not be improved, increase its trial counter*/
                trial[i] = trial[i] + 1;
        } /*if */
        i++;
        if (i == FoodNumber)
            i = 0;
    }/*while*/

    /*end of onlooker bee phase     */
}
//==============================================================
// Determines the food sources whose trial counter exceeds the "limit" value. 
// In Basic ABC, only one scout is allowed to occur in each cycle       
//==============================================================
void SendScoutBees()
{
    int maxtrialindex, i;
    maxtrialindex = 0;
    for (i = 1; i < FoodNumber; i++)
    {
        if (trial[i] > trial[maxtrialindex])
            maxtrialindex = i;
    }
    if (trial[maxtrialindex] >= limit)
        init(maxtrialindex);
}

private void button3_Click(object sender, EventArgs e)
{
    openFileDialog2.Filter = "Text Files (*.txt) | *.txt|" + "CSV Files (*.csv) | *.csv|" + "All Files (*.*)| *.*";
    openFileDialog2.FilterIndex = 1;
    openFileDialog2.Title = "انتخاب مجموعه داده ها برای استخراج الگوهای تکرارشونده";
    if (openFileDialog2.ShowDialog() == DialogResult.OK)
    {
        strfilename1 = openFileDialog2.FileName;
        StreamReader sd = new StreamReader(strfilename1);
        while (sd.EndOfStream == false)
        {
            string nextline = sd.ReadLine();
            string[] strword = nextline.Split(' ', ',');
            trans_length[items_number - 1, 0] = items_number - 1;
            trans_length[items_number - 1, 1] = strword.Length;

            for (int j = 0; j < strword.Length; j++)
            {
                if (strword[j] != "")
                {
                    if (input_items[0] == null)
                    {
                        input_items[0] = strword[j].Trim();
                        input_file[0, 0] = strword[j].Trim();
                        items_number++;
                    }
                    else
                    {
                        bool find = false;
                        for (int i = 0; i < items_number; i++)
                        {
                            if (string.Equals(input_items[i], strword[j].Trim()) == true)
                            {
                                find = true;
                                input_file[trans_number, j] = strword[j].Trim();
                                break;
                            }
                        }
                        if (find == false)
                        {
                            input_items[items_number] = strword[j].Trim();
                            input_file[trans_number, j] = strword[j].Trim();
                            items_number++;
                        }
                    }
                }
            }
            trans_number++;
        }
    }
}

private void button15_Click(object sender, EventArgs e)
{
    FolderBrowserDialog fb = new FolderBrowserDialog();
    if (fb.ShowDialog() == DialogResult.OK)
    {
        string path = fb.SelectedPath + @"\Sanitized dataset.txt";
        if (!File.Exists(path))
        {
            using (StreamWriter sw = File.CreateText(path))
            {
                for (int i = 0; i < trans_number; i++)
                {
                    string set = "";
                    int next = 0;
                    while (input_file[i, next] != null)
                    {
                        if (set != "")
                            set = set + "," + input_file[i, next].ToString();
                        else
                            set = input_file[i, next].ToString();
                        next++;
                    }
                    sw.WriteLine(set);
                }
            }
        }
    }
}
        public void CrtRnd_pi()
        {
            Random rnd = new Random();
            intrnd_pi = rnd.Next(0, D);
        }

        void Dissimilarity_func(int index_i, int[] array_VS)
        {
            for (int i = 0; i < D; i++)
            {
                if (array_VS[i] == 1 && Population[index_i, i] == 1)
                {
                    M11++;
                    n1++;
                }
                if (array_VS[i] == 1 && Population[index_i, i] == 0)
                {
                    M10++;
                    n1++;
                }
                else
                {
                    M01++;
                    n0++;
                }
            }
            Dissimilarity = 1 - (Convert.ToSingle(M11) / (Convert.ToSingle(M11) + Convert.ToSingle(M10) + Convert.ToSingle(M11)));
        }

        void Calculatebits()
        {
            Random rnd = new Random();
            for (int i = 1; i <= n1 - M11; i++)
            {
                M11_new = M11 + i;
                M01_new = n1 - M11_new;
                M10_new = rnd.Next(1, n0 - 1);
            }
            //M11_new = M11 + rnd.Next(1, n1 - M11);

            Random rnd_M10 = new Random();
            M10_new = rnd_M10.Next(1,n0-1);
            Dissimilarity_new = 1 - (Convert.ToSingle(M11) / (Convert.ToSingle(M11) + Convert.ToSingle(M10) + Convert.ToSingle(M11)));
        }
        void RandomVectors()
        {
            /*A randomly chosen solution is used in producing a mutant solution of the solution i*/
            CrtRnd_pi();
            r = Convert.ToSingle(intrnd_pi) / 100;
            neighbour1 = (int)(r * FoodNumber);

            /*A randomly chosen solution is used in producing a mutant solution of the solution i*/
            CrtRnd_pi();
            r = Convert.ToSingle(intrnd_pi) / 100;
            neighbour2 = (int)(r * FoodNumber);
        }

        private void button5_Click(object sender, EventArgs e)
        {
            openFileDialog1.Filter = "Text Files (*.txt) | *.txt|" + "CSV Files (*.csv) | *.csv|" + "All Files (*.*)| *.*";
            openFileDialog1.FilterIndex = 1;
            openFileDialog1.Title = "انتخاب فایل پشتیبانی برای قوانین حساس";
            if (openFileDialog1.ShowDialog() == DialogResult.OK)
            {
                strfilename1 = openFileDialog1.FileName;
                StreamReader sd = new StreamReader(@strfilename1);
                while (sd.EndOfStream == false)
                {
                    string nextline = sd.ReadLine();
                    index_sensitive[sensitive_count] = Convert.ToInt32(nextline);
                    sensitive_count++;
                }
                txt_count_SRs.Text = rule_index.ToString();
            }
        }
    }
}
